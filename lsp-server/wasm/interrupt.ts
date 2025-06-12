/**
 * Allows to signal the worker that it is requested to interrupt its current
 * computation.
 * The page signals the worker by incrementing a 32-bit shared integer.
 * The worker periodically checks the integer, and would eventually break
 * its execution if the integer has been modified since the last time it was
 * read.
 */
class WorkerInterrupts {

    debug : boolean = false;
    vec: Uint32Array
    checkpoint: number = 0

    setup(vec: Uint32Array) {
        console.log("Interrupt Support Enabled (server)");
        this.vec = vec;
    }

    pending(): boolean {
        if (this.vec && typeof Atomics !== 'undefined') {
            var ld = Atomics.load(this.vec, 0);
            if (ld > this.checkpoint) {
              if (this.debug) console.log("Rocq has been interrupted!");
                this.checkpoint = ld;
                return true;
            }
        }
        return false;
    }
}

export { WorkerInterrupts }
