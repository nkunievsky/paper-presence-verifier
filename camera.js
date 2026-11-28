import {canonical} from "./verify.js";

import {verifyMapReceipt} from "./map-receipt.mjs";
const mapPolicy = "camera-minute-3-yunet-output-maps-v1";
let verifier;
const policy = "camera-minute-3-experimental-v1";
const text = new TextEncoder();
const hex = bytes => Array.from(new Uint8Array(bytes),x=>x.toString(16).padStart(2,"0")).join("");
const raw = h => Uint8Array.from(h.match(/../g),x=>parseInt(x,16));
const sha = async b => hex(await crypto.subtle.digest("SHA-256",b));
const hash = obj => sha(text.encode(canonical(obj)));
const hashPattern = /^[0-9a-f]{64}$/;

export async function verifyCamera(report,work,credential,signature,known,creditedSeconds) {
  const fail = () => { throw Error("Invalid or incomplete timestamped camera sequence."); };
  if (report?.scope !== "disclosed-history-only" || ![policy,mapPolicy].includes(report.policy) ||
      !Array.isArray(report.runs) || !Array.isArray(report.slots) || !report.slots.length ||
      report.slots.length > 1440 || !hashPattern.test(credential)) fail();
  const {cameraTimestamp,cameraProof} = await import("./engine.bundle.js");
  const seed = await sha(raw(credential));
  const key = await crypto.subtle.importKey("raw",raw(seed),{name:"HMAC",hash:"SHA-256"},false,["sign"]);
  let previous = "00".repeat(32), index = 0, priorEnd = 0, availableSeconds = 0;
  for (const pair of report.runs) {
    if (!Array.isArray(pair) || pair.length !== 2) fail();
    const [start,end] = pair;
    if (!Number.isSafeInteger(start) || !Number.isSafeInteger(end) || start < priorEnd || start > end) fail();
    priorEnd = end;
    availableSeconds += Math.max(0,Math.floor(end/1000)-Math.ceil(start/1000));
    for (let minute=Math.ceil(start/60000); minute<Math.floor(end/60000); minute++) {
      const item = report.slots[index++];
      if (!item || minute > 100000000) fail();
      const b = item.entry?.body;
      const enrollment = await hash([policy,{work,credential,first_minute:minute,minutes:1,seed}]);
      if (!b || b.enrollment !== enrollment || b.policy !== report.policy || b.minute !== minute ||
          b.previous !== previous || !hashPattern.test(b.commitment) || !hashPattern.test(b.jpeg_commitment) ||
          Object.keys(b).sort().join() !== "commitment,enrollment,jpeg_commitment,minute,policy,previous,times_ms") fail();
      const msg = text.encode(canonical([policy,credential,minute]));
      let offset;
      for (let c=0;c<256 && offset===undefined;c++) {
        const draw = new Uint8Array(await crypto.subtle.sign("HMAC",key,new Uint8Array([...msg,c])));
        const n = draw.find(v=>v<250);
        if (n!==undefined) offset = (n%50)*1000;
      }
      const t=b.times_ms;
      if (offset===undefined || !Array.isArray(t) || t.length!==3 || !t.every(Number.isSafeInteger) ||
          t[0]<offset || t[0]>offset+2000 ||
          !t.slice(1).every((v,i)=>v-t[i]>=650 && v-t[i]<=2500)) fail();
      await signature(credential,item.entry.signature,b);
      previous = await hash(b);
      const id = credential + "/" + minute;
      if (known.has(id) && known.get(id)!==previous) throw Error("Conflicting camera histories for the same minute.");
      known.set(id,previous);
      const issued = await cameraTimestamp(text.encode(canonical(item.entry)),item);
      if (!(issued >= minute*60000+Math.floor(t[2]/1000)*1000 && issued <= minute*60000+75000)) fail();
      const {commitment,...header}=b;
      if (report.policy === mapPolicy) {
        if (typeof item.proof !== "string" || item.proof.length > 4*Math.ceil(4*1024*1024/3)) fail();
        verifier ??= await WebAssembly.compile(await (await fetch(new URL("./circuits/camera-map.wasm",import.meta.url))).arrayBuffer());
        verifyMapReceipt(verifier,raw(commitment),Uint8Array.from(atob(item.proof), c=>c.charCodeAt(0)));
      } else await cameraProof(item.proof,raw(await hash(header)+commitment));
    }
  }
  if (index!==report.slots.length) fail();
  if (!Number.isSafeInteger(creditedSeconds) || creditedSeconds < 0 || creditedSeconds > availableSeconds)
    throw Error("The registry's credited duration is inconsistent with its disclosed camera recording intervals.");
  return index;
}
