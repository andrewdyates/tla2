// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::VecDeque;
use std::fs::{self, File};
use std::io::{self, BufReader, BufWriter, Read, Write};
use std::path::Path;
use std::time::{Instant, SystemTime};

use serde::de::DeserializeOwned;
use serde::{Deserialize, Serialize};

use super::config::{
    CheckpointConfig, ExplorationConfig, ExplorationObserver, ExplorationResult,
    ParallelExplorationObserver, DEADLINE_CHECK_INTERVAL,
};
use super::fingerprint::fingerprint_marking;
use super::seen::{LocalSeenSet, LookupOutcome};
use super::setup::ExplorationSetup;
use super::transition_selection::enabled_transitions_into;
use crate::marking::{pack_marking_config, unpack_marking_config};
use crate::petri_net::PetriNet;
use crate::stubborn::{DependencyGraph, PorStrategy};

const CHECKPOINT_VERSION: u32 = 1;
const MANIFEST_FILE: &str = "checkpoint.json";
const FINGERPRINTS_FILE: &str = "fingerprints.bin";
const FRONTIER_FILE: &str = "frontier.bin";

#[derive(Debug, Serialize, Deserialize)]
struct CheckpointManifest<S> {
    version: u32,
    created_at: u64,
    observer_kind: String,
    num_places: usize,
    num_transitions: usize,
    packed_bytes: usize,
    excluded: Vec<bool>,
    seen_states: usize,
    frontier_states: usize,
    observer: S,
}

struct LoadedCheckpoint<S> {
    observer: S,
    seen_fingerprints: Vec<u128>,
    frontier: VecDeque<Box<[u8]>>,
}

/// Observer snapshots that can be persisted and restored across runs.
pub(crate) trait CheckpointableObserver: ExplorationObserver {
    type Snapshot: Serialize + DeserializeOwned;

    const CHECKPOINT_KIND: &'static str;

    fn snapshot(&self) -> Self::Snapshot;

    fn restore_from_snapshot(&mut self, snapshot: Self::Snapshot);
}

pub(crate) fn explore_checkpointable_observer<O>(
    net: &PetriNet,
    config: &ExplorationConfig,
    observer: &mut O,
) -> io::Result<ExplorationResult>
where
    O: ParallelExplorationObserver + CheckpointableObserver,
{
    let checkpoint = config
        .checkpoint()
        .expect("checkpointed exploration requires ExplorationConfig::with_checkpoint");
    if config.workers() > 1 {
        eprintln!(
            "checkpoint mode currently runs sequentially; ignoring workers={}",
            config.workers()
        );
    }

    let ExplorationSetup {
        marking_config,
        pack_capacity,
        num_places,
        num_transitions,
        initial_packed,
    } = ExplorationSetup::analyze(net);
    let packed_bytes = marking_config.packed_len * marking_config.width.bytes();

    let dep_graph = match &config.por_strategy {
        PorStrategy::None => None,
        _ => Some(DependencyGraph::build(net)),
    };

    let mut visited = LocalSeenSet::new();
    let mut queue: VecDeque<Box<[u8]>> = VecDeque::new();
    let mut resumed = false;

    if checkpoint.resume && checkpoint_exists(&checkpoint.dir) {
        let loaded = load_checkpoint::<O::Snapshot>(
            checkpoint,
            num_places,
            num_transitions,
            packed_bytes,
            marking_config.excluded_places(),
            O::CHECKPOINT_KIND,
        )?;
        observer.restore_from_snapshot(loaded.observer);
        for fp in loaded.seen_fingerprints {
            visited.insert_checked(fp);
        }
        queue = loaded.frontier;
        resumed = true;
    }

    if !resumed {
        if !observer.on_new_state(&net.initial_marking) {
            return Ok(ExplorationResult::new(false, 1, true));
        }
        visited.insert_checked(fingerprint_marking(&initial_packed));
        queue.push_back(initial_packed);
    }

    if observer.is_done() {
        persist_checkpoint(
            checkpoint,
            num_places,
            num_transitions,
            packed_bytes,
            marking_config.excluded_places(),
            observer,
            &visited,
            &queue,
        )?;
        return Ok(ExplorationResult::new(false, visited.len(), true));
    }

    let mut stopped_by_observer = false;
    let mut completed = true;
    let mut current_tokens = Vec::with_capacity(num_places);
    let mut deadline_counter: u32 = 0;
    let mut pack_buf = Vec::with_capacity(pack_capacity);
    let mut enabled_transitions = Vec::with_capacity(num_transitions);
    let mut states_since_checkpoint = 0usize;

    while let Some(current_packed) = queue.pop_front() {
        deadline_counter = deadline_counter.wrapping_add(1);
        if deadline_counter.is_multiple_of(DEADLINE_CHECK_INTERVAL)
            && config
                .deadline()
                .is_some_and(|deadline| Instant::now() >= deadline)
        {
            completed = false;
            break;
        }

        if observer.is_done() {
            stopped_by_observer = true;
            break;
        }

        unpack_marking_config(&current_packed, &marking_config, &mut current_tokens);

        enabled_transitions_into(
            net,
            &current_tokens,
            num_transitions,
            dep_graph.as_ref(),
            &config.por_strategy,
            &mut enabled_transitions,
        );

        let has_enabled = !enabled_transitions.is_empty();

        for &trans in &enabled_transitions {
            net.apply_delta(&mut current_tokens, trans);

            if !observer.on_transition_fire(trans) {
                stopped_by_observer = true;
                net.undo_delta(&mut current_tokens, trans);
                break;
            }

            pack_marking_config(&current_tokens, &marking_config, &mut pack_buf);
            let fp = fingerprint_marking(&pack_buf);
            if visited.contains_checked(&fp) == LookupOutcome::Present {
                net.undo_delta(&mut current_tokens, trans);
                continue;
            }

            if visited.len() >= config.max_states() {
                completed = false;
                net.undo_delta(&mut current_tokens, trans);
                break;
            }

            if !observer.on_new_state(&current_tokens) {
                stopped_by_observer = true;
                net.undo_delta(&mut current_tokens, trans);
                break;
            }

            visited.insert_checked(fp);
            queue.push_back(pack_buf.as_slice().into());
            net.undo_delta(&mut current_tokens, trans);
        }

        if stopped_by_observer || !completed {
            break;
        }

        if !has_enabled {
            observer.on_deadlock(&current_tokens);
            if observer.is_done() {
                stopped_by_observer = true;
                break;
            }
        }

        states_since_checkpoint += 1;
        if states_since_checkpoint >= checkpoint.interval_states {
            persist_checkpoint(
                checkpoint,
                num_places,
                num_transitions,
                packed_bytes,
                marking_config.excluded_places(),
                observer,
                &visited,
                &queue,
            )?;
            states_since_checkpoint = 0;
            #[cfg(test)]
            if checkpoint.stop_after_first_save {
                return Ok(ExplorationResult::new(false, visited.len(), false));
            }
        }
    }

    persist_checkpoint(
        checkpoint,
        num_places,
        num_transitions,
        packed_bytes,
        marking_config.excluded_places(),
        observer,
        &visited,
        &queue,
    )?;

    Ok(ExplorationResult::new(
        completed && !stopped_by_observer && queue.is_empty(),
        visited.len(),
        stopped_by_observer,
    ))
}

fn checkpoint_exists(dir: &Path) -> bool {
    dir.join(MANIFEST_FILE).exists()
}

fn persist_checkpoint<O>(
    checkpoint: &CheckpointConfig,
    num_places: usize,
    num_transitions: usize,
    packed_bytes: usize,
    excluded: &[bool],
    observer: &O,
    visited: &LocalSeenSet,
    queue: &VecDeque<Box<[u8]>>,
) -> io::Result<()>
where
    O: CheckpointableObserver,
{
    let manifest = CheckpointManifest {
        version: CHECKPOINT_VERSION,
        created_at: SystemTime::now()
            .duration_since(SystemTime::UNIX_EPOCH)
            .map(|duration| duration.as_secs())
            .unwrap_or(0),
        observer_kind: O::CHECKPOINT_KIND.to_string(),
        num_places,
        num_transitions,
        packed_bytes,
        excluded: excluded.to_vec(),
        seen_states: visited.len(),
        frontier_states: queue.len(),
        observer: observer.snapshot(),
    };
    save_checkpoint_files(
        &checkpoint.dir,
        &manifest,
        &visited.collect_fingerprints(),
        queue,
    )
}

fn save_checkpoint_files<S: Serialize>(
    dir: &Path,
    manifest: &CheckpointManifest<S>,
    fingerprints: &[u128],
    frontier: &VecDeque<Box<[u8]>>,
) -> io::Result<()> {
    let saving_dir = dir.with_extension("saving");
    let old_dir = dir.with_extension("old");

    if saving_dir.exists() {
        fs::remove_dir_all(&saving_dir)?;
    }
    if old_dir.exists() {
        fs::remove_dir_all(&old_dir)?;
    }

    fs::create_dir_all(&saving_dir)?;
    write_manifest(&saving_dir.join(MANIFEST_FILE), manifest)?;
    write_fingerprints(&saving_dir.join(FINGERPRINTS_FILE), fingerprints)?;
    write_frontier(&saving_dir.join(FRONTIER_FILE), frontier)?;

    if dir.exists() {
        fs::rename(dir, &old_dir)?;
    }
    if let Err(error) = fs::rename(&saving_dir, dir) {
        if old_dir.exists() {
            let _ = fs::rename(&old_dir, dir);
        }
        return Err(error);
    }

    if let Some(parent) = dir.parent() {
        if let Ok(parent_dir) = File::open(parent) {
            let _ = parent_dir.sync_all();
        }
    }
    if old_dir.exists() {
        let _ = fs::remove_dir_all(&old_dir);
    }
    Ok(())
}

fn write_manifest<S: Serialize>(path: &Path, manifest: &CheckpointManifest<S>) -> io::Result<()> {
    let file = File::create(path)?;
    let mut writer = BufWriter::new(file);
    serde_json::to_writer_pretty(&mut writer, manifest)
        .map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error))?;
    writer.flush()?;
    writer.get_ref().sync_all()?;
    Ok(())
}

fn write_fingerprints(path: &Path, fingerprints: &[u128]) -> io::Result<()> {
    let file = File::create(path)?;
    let mut writer = BufWriter::new(file);
    writer.write_all(&(fingerprints.len() as u64).to_le_bytes())?;
    for fingerprint in fingerprints {
        writer.write_all(&fingerprint.to_le_bytes())?;
    }
    writer.flush()?;
    writer.get_ref().sync_all()?;
    Ok(())
}

fn write_frontier(path: &Path, frontier: &VecDeque<Box<[u8]>>) -> io::Result<()> {
    let file = File::create(path)?;
    let mut writer = BufWriter::new(file);
    writer.write_all(&(frontier.len() as u64).to_le_bytes())?;
    for state in frontier {
        writer.write_all(&(state.len() as u64).to_le_bytes())?;
        writer.write_all(state)?;
    }
    writer.flush()?;
    writer.get_ref().sync_all()?;
    Ok(())
}

fn load_checkpoint<S: DeserializeOwned>(
    checkpoint: &CheckpointConfig,
    num_places: usize,
    num_transitions: usize,
    packed_bytes: usize,
    excluded: &[bool],
    observer_kind: &str,
) -> io::Result<LoadedCheckpoint<S>> {
    let manifest_path = checkpoint.dir.join(MANIFEST_FILE);
    let file = File::open(&manifest_path)?;
    let reader = BufReader::new(file);
    let manifest: CheckpointManifest<S> = serde_json::from_reader(reader)
        .map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error))?;

    if manifest.version != CHECKPOINT_VERSION {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!(
                "checkpoint version mismatch: expected {}, got {}",
                CHECKPOINT_VERSION, manifest.version
            ),
        ));
    }
    if manifest.observer_kind != observer_kind {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!(
                "checkpoint observer mismatch: expected {observer_kind}, got {}",
                manifest.observer_kind
            ),
        ));
    }
    if manifest.num_places != num_places || manifest.num_transitions != num_transitions {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "checkpoint net shape does not match the current model",
        ));
    }
    if manifest.packed_bytes != packed_bytes {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "checkpoint packed-state width does not match the current model",
        ));
    }
    if manifest.excluded != excluded {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "checkpoint implied-place layout does not match the current model",
        ));
    }

    let seen_fingerprints = read_fingerprints(&checkpoint.dir.join(FINGERPRINTS_FILE))?;
    if seen_fingerprints.len() != manifest.seen_states {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!(
                "checkpoint fingerprint count mismatch: manifest={}, file={}",
                manifest.seen_states,
                seen_fingerprints.len()
            ),
        ));
    }
    let frontier = read_frontier(
        &checkpoint.dir.join(FRONTIER_FILE),
        manifest.frontier_states,
        packed_bytes,
    )?;
    Ok(LoadedCheckpoint {
        observer: manifest.observer,
        seen_fingerprints,
        frontier,
    })
}

fn read_fingerprints(path: &Path) -> io::Result<Vec<u128>> {
    let file = File::open(path)?;
    let mut reader = BufReader::new(file);
    let mut len_bytes = [0u8; 8];
    reader.read_exact(&mut len_bytes)?;
    let len = u64::from_le_bytes(len_bytes) as usize;
    let mut fingerprints = Vec::with_capacity(len);
    for _ in 0..len {
        let mut fp_bytes = [0u8; 16];
        reader.read_exact(&mut fp_bytes)?;
        fingerprints.push(u128::from_le_bytes(fp_bytes));
    }
    Ok(fingerprints)
}

fn read_frontier(
    path: &Path,
    expected_len: usize,
    packed_bytes: usize,
) -> io::Result<VecDeque<Box<[u8]>>> {
    let file = File::open(path)?;
    let mut reader = BufReader::new(file);
    let mut len_bytes = [0u8; 8];
    reader.read_exact(&mut len_bytes)?;
    let len = u64::from_le_bytes(len_bytes) as usize;
    if len != expected_len {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!("checkpoint frontier length mismatch: manifest={expected_len}, file={len}"),
        ));
    }
    let mut frontier = VecDeque::with_capacity(len);
    for _ in 0..len {
        let mut state_len_bytes = [0u8; 8];
        reader.read_exact(&mut state_len_bytes)?;
        let state_len = u64::from_le_bytes(state_len_bytes) as usize;
        if state_len != packed_bytes {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!(
                    "checkpoint packed-state length mismatch: expected {packed_bytes}, got {state_len}"
                ),
            ));
        }
        let mut state = vec![0u8; state_len];
        reader.read_exact(&mut state)?;
        frontier.push_back(state.into_boxed_slice());
    }
    Ok(frontier)
}
