// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use dashmap::DashMap;
use tower_lsp::lsp_types::Url;
use tower_lsp::Client;

use crate::document::DocumentState;

/// TLA+ Language Server backend
pub struct TlaBackend {
    /// LSP client for sending notifications
    pub(crate) client: Client,
    /// Open documents
    pub(crate) documents: DashMap<Url, DocumentState>,
}

impl TlaBackend {
    pub fn new(client: Client) -> Self {
        Self {
            client,
            documents: DashMap::new(),
        }
    }
}
