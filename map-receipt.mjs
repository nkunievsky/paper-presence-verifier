// One bounded instance per untrusted receipt. The verifier needs no filesystem,
// environment variables, clocks, network, randomness, or host cryptography.
export function verifyMapReceipt(module, root, proof) {
  if (root.length !== 32 || !proof.length || proof.length > 4*1024*1024) throw Error("Invalid YuNet proof length");
  const instance = new WebAssembly.Instance(module, {wasi_snapshot_preview1:{
    environ_sizes_get(a,b) {
      const view = new DataView(instance.exports.memory.buffer);
      view.setUint32(a,0,true); view.setUint32(b,0,true); return 0;
    },
    environ_get() {return 0;}, fd_write() {return 8;},
    proc_exit() {throw Error("Camera verifier exited");}
  }});
  const {memory,input_ptr,verify} = instance.exports;
  const offset = input_ptr();
  const data = new Uint8Array(memory.buffer);
  data.set(root,offset); data.set(proof,offset+32);
  if (verify(proof.length)!==1) throw Error("Invalid YuNet output-map proof or checkpoint");
}
