// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#[derive(Default)]
struct Widget {
    _t: countme::Count<Self>,
}

fn main() {
    let w1 = Widget::default();
    let _w2 = Widget::default();
    drop(w1);
    let _w3 = Widget::default();
}
