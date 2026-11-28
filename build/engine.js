import { createEVM } from "@ethereumjs/evm";

let machine;
const programs = new Map();
function putWord(buffer, offset, value) {
  new DataView(buffer.buffer).setUint32(offset + 28, value);
}
export async function checkProof(circuit, proof, expected) {
  const [byteLength, fieldCount] = circuit === "activity" ? [4896, 18] : [4576, 49];
  if (proof?.proof?.length !== byteLength || !Array.isArray(proof.proof) ||
      !proof.proof.every(v => Number.isInteger(v) && v >= 0 && v <= 255) ||
      expected.length !== fieldCount || proof.instances?.length !== 1 ||
      !Array.isArray(proof.instances[0]) || proof.instances[0].length !== fieldCount ||
      !expected.every((v,i) => typeof v === "string" && /^[0-9a-f]{64}$/.test(v) && proof.instances[0][i] === v)) {
    throw Error("A proof has invalid bytes or public inputs for this paper.");
  }
  if (!programs.has(circuit)) {
    const response = await fetch(new URL("./circuits/" + circuit + ".bin", import.meta.url));
    if (!response.ok) throw Error("The proof verifier could not be loaded. Reload and try again.");
    programs.set(circuit, new Uint8Array(await response.arrayBuffer()));
  }
  machine ??= await createEVM();
  // ABI for verifyProof(bytes,uint256[]). EZKL encodes public field strings little-endian.
  const data = new Uint8Array(132 + byteLength + 32 * fieldCount);
  data.set([0x1e,0x8e,0x1e,0x13]);
  putWord(data,4,64);
  putWord(data,36,96 + byteLength);
  putWord(data,68,byteLength);
  data.set(proof.proof,100);
  putWord(data,100 + byteLength,fieldCount);
  expected.forEach((hex, i) => data.set(hex.match(/../g).map(v => parseInt(v,16)).reverse(),132 + byteLength + 32*i));
  const result = await machine.runCode({code: programs.get(circuit), data, gasLimit: 30000000n});
  const value = result.returnValue;
  if (result.exceptionError || value.length !== 32 || value[31] !== 1 || !value.subarray(0,31).every(x => x === 0)) {
    throw Error("An embedded zero-knowledge proof failed cryptographic verification.");
  }
}

export {cameraTimestamp} from "./camera.js";

export async function cameraProof(encoded, fields) {
  const raw = Uint8Array.from(atob(encoded), c => c.charCodeAt(0));
  if (raw.length !== 10304 || fields.length !== 64) throw Error("Invalid camera proof dimensions.");
  if (!programs.has("camera")) {
    const r = await fetch(new URL("./circuits/camera.bin",import.meta.url));
    if (!r.ok) throw Error("Unable to load camera verifier.");
    programs.set("camera",new Uint8Array(await r.arrayBuffer()));
  }
  const data = new Uint8Array(132 + raw.length + 32*fields.length);
  // verify(bytes,bytes32[])
  data.set([0xea,0x50,0xd0,0xe4]);
  putWord(data,4,64);
  putWord(data,36,96 + raw.length);
  putWord(data,68,raw.length);
  data.set(raw,100);
  putWord(data,100 + raw.length,fields.length);
  fields.forEach((v,i) => putWord(data,132 + raw.length + 32*i,v));
  machine ??= await createEVM();
  const r = await machine.runCode({code:programs.get("camera"),data,gasLimit:60000000n});
  if (r.exceptionError || r.returnValue.length !== 32 || r.returnValue[31] !== 1 ||
      r.returnValue.subarray(0,31).some(x => x !== 0)) throw Error("Camera window proof did not verify.");
}
