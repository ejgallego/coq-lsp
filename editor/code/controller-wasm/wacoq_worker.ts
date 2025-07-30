import { IcoqPod } from './core';

function postMessage(msg) {
    (<any>self).postMessage(msg);
}

async function main(baseURI : string) {

  // We can only really start when we get the real baseURI from the extension side.
    let binDir = baseURI + "/controller-wasm/out/";
    let nmDir = baseURI + "/controller-wasm/node_modules/";
    var icoq = new IcoqPod(binDir, nmDir);

    postMessage(['Starting']);
    icoq.on('message', postMessage);
    icoq.on('progress', ev => postMessage(['LibProgress', ev]));

    addEventListener('message', (msg) => {
        icoq.command(msg.data);
    });

    await icoq.boot();

    postMessage(['Boot']);

    Object.assign(global, {icoq});
}

async function main_get_dir() {

  // First messages _must_ be the baseUri
  addEventListener('message', (event) => {
    main(event.data);
  }, { once: true } );

}

main_get_dir();
