import { IcoqPod } from './core';

function postMessage(msg) {
    (<any>self).postMessage(msg);
}

async function main(baseURI : string) {

    // We can only really start when we get the real baseURI from the extension side.
    let binDir = baseURI + "/wasm-bin/";
    let nmDir = baseURI + "/wasm-bin/node_modules/";

    let arr = [];

    // We buffer init messages
    const pushMsg = (msg) => {
        arr.push(msg.data);
    }
    addEventListener('message', pushMsg);

    // start ICoq
    var icoq = new IcoqPod(binDir, nmDir);

    icoq.on('message', postMessage);

    await icoq.boot();

    arr.forEach((a) => {
      icoq.command(a)
    });

    // Remove the previous one
    addEventListener('message', (msg) => {
        icoq.command(msg.data);
    });

    removeEventListener('message', pushMsg);

    // Idle loop
    setInterval(() => {
        icoq.idle();
    }, 200);

    Object.assign(global, {icoq});
}

async function main_get_dir() {

  // First messages _must_ be the baseUri
  addEventListener('message', (event) => {
    main(event.data);
  }, { once: true } );

}

main_get_dir();

// Local Variables:
// typescript-indent-level: 4
// End:
