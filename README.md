# bacon_rajan_cc (fork)
This is a fork of bacon_rajan_cc by https://github.com/fitzgen aiming to introduce the modifications
useful for the purposes of Ves:

1. [x] Use allocation contexts instead of a thread local to allow multiple independent object graphs within the same runtime.
2. [x] Provide an API for accessing raw internal Rc pointers.
3. [ ] Make CcContext and Cc thread-safe (possibly gated behind a feature)
4. [ ] Provide a way to automatically trigger cycle collection after a number of potential cycle roots exceeds a threshold.
5. [ ] Implement concurrent collection.

## Original Readme

`Cc<T>`: A reference counted type with cycle collection for Rust. Concurrent or
stop-the-world. Based on the paper
["Concurrent Cycle Collection in Reference Counted Systems"][paper] by David
F. Bacon and V.T. Rajan. [JVM implementation](https://github.com/JikesRVM/JikesRVM/blob/8f6ac1854a73059595587b63fb4e8a3553bc7ff1/rvm/src/vm/memoryManagers/concurrent/VM_Allocator.java)

Currently only stop-the-world, not concurrent.

## Usage

Add to `Cargo.toml`:

Note this requires at least Rust 1.28 for the std::alloc api's.

```toml
[dependencies]
bacon_rajan_cc = "0.2"
```

Then, in your crate:

```rust
extern crate bacon_rajan_cc;
use bacon_rajan_cc::{CcContext, Cc, Trace, Tracer};
```

## Alternatives
- https://github.com/withoutboats/shifgrethor
- https://github.com/Manishearth/rust-gc
- https://github.com/Others/shredder
- https://github.com/jazz-lang/wafflelink (conservative on stack,precise on heap Immix Mark-Region GC with evacuation in Rust)
