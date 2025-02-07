// Provides: interrupt_setup
function interrupt_setup(shmem) {
    var Int32Array = globalThis.Int32Array,
        SharedArrayBuffer = globalThis.SharedArrayBuffer;

    if (Int32Array && SharedArrayBuffer) {
        shmem = shmem || new Int32Array(new SharedArrayBuffer(4));
        interrupt_setup.vec = shmem;
        interrupt_setup.checkpoint = 0;
        return shmem;
    }
}

// Provides: interrupt_pending
// Requires: interrupt_setup
function interrupt_pending() {
    var Atomics = globalThis.Atomics;

    if (Atomics && interrupt_setup.vec) {
        var ld = Atomics.load(interrupt_setup.vec, 0);
        if (ld > interrupt_setup.checkpoint) {
            interrupt_setup.checkpoint = ld;
            return true;
        }
    }
    return false;
}
