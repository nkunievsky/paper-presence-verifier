import { singleFacePad, padPolicy, policy, model } from "./policies.js";

export const defaultTrust = {
  registry_id: "94293088-5a7f-436b-8644-b5bf61d0bf8f",
  public_key: "5609e907aac6e9feede098da7a54c7670eb381eb35125ebf98869d4d8fafcb12"
};
const text = new TextEncoder();
const decoder = new TextDecoder("utf-8",{fatal:true});
const digestPattern = /^[0-9a-f]{64}$/;
const integer = n => Number.isSafeInteger(n) && n >= 0;
function check(ok, message) { if (!ok) throw Error(message); }
function same(a,b) { return canonical(a) === canonical(b); }
export function canonical(v) {
  if (Array.isArray(v)) return "[" + v.map(canonical).join(",") + "]";
  if (v !== null && typeof v === "object") return "{" + Object.keys(v).sort().map(k => canonical(k)+":"+canonical(v[k])).join(",") + "}";
  return JSON.stringify(v).replace(/[\x7f-\uffff]/g, c => "\\u" + c.charCodeAt(0).toString(16).padStart(4,"0"));
}
function hex(bytes) { return Array.from(bytes,b => b.toString(16).padStart(2,"0")).join(""); }
async function sha(bytes) { return hex(new Uint8Array(await crypto.subtle.digest("SHA-256",bytes))); }
const hashObject = value => sha(text.encode(canonical(value)));
async function signature(publicKey, sig, body) {
  check(typeof publicKey === "string" && digestPattern.test(publicKey) && typeof sig === "string" && /^[0-9a-f]{128}$/.test(sig), "Invalid Ed25519 key or signature format.");
  const bytes = value => Uint8Array.from(value.match(/../g),v => parseInt(v,16));
  let key;
  try { key = await crypto.subtle.importKey("raw",bytes(publicKey),"Ed25519",false,["verify"]); }
  catch { throw Error("This browser could not open the Ed25519 key. Try a current browser."); }
  check(await crypto.subtle.verify("Ed25519",key,bytes(sig),text.encode(canonical(body))),"The signature does not match the trusted registry key or signed data.");
}
async function matchPDF(pdf, cert, trust) {
  const p = cert.payload;
  check(new TextDecoder().decode(pdf.subarray(0,5)) === "%PDF-", "The selected document has no PDF header. Use the PDF file itself.");
  if (await sha(pdf) === p.pdf_sha256) return "Original certified PDF";
  const marker = "\n%PaperPresence-Publication-1 ";
  const tailOffset = Math.max(0,pdf.length-8192-marker.length);
  const tail = new TextDecoder("latin1").decode(pdf.subarray(tailOffset));
  const pos = tail.lastIndexOf(marker);
  check(pos >= 0,"The PDF differs from the certified edition. Use the exact finalized or signed publication PDF.");
  const body = pdf.subarray(0,tailOffset+pos);
  const xref = /startxref\s+([0-9]+)\s+%%EOF\s*$/.exec(new TextDecoder("latin1").decode(body.slice(-256)));
  check(xref,"The publication copy has an invalid PDF trailer.");
  const ending = "\nstartxref\n"+xref[1]+"\n%%EOF\n";
  check(tail.endsWith(ending),"The publication trailer has changed.");
  const encoded = tail.slice(pos+marker.length,-ending.length);
  check(/^[A-Za-z0-9+/]+={0,2}$/.test(encoded) && encoded.length % 4 === 0,"Invalid publication signature encoding.");
  const env = JSON.parse(decoder.decode(Uint8Array.from(atob(encoded),c=>c.charCodeAt(0))));
  const m = env.manifest;
  await signature(trust.public_key,env.signature,m);
  check(m.kind === "paper-presence-publication-v1" && m.registry === p.registry_id && m.allocation === p.allocation_id &&
    integer(m.original_length) && m.original_length > 0 && m.original_length < body.length &&
    m.certificate_sha256 === await hashObject(cert) && m.annotated_body_sha256 === await sha(body) &&
    p.pdf_sha256 === await sha(body.subarray(0,m.original_length)), "The publication copy does not match the certificate.");
  if (m.proof_url !== "certificate.json") {
    const url = new URL(m.proof_url);
    check(url.protocol === "https:" && !url.username && !url.password && /^[!-~]{1,1500}$/.test(m.proof_url) && !m.proof_url.includes("\\"),"Invalid signed publication link.");
  }
  return "Signed publication copy";
}
function markers(body,seen) {
  check(Array.isArray(body.nullifiers) && integer(body.credited_seconds) && body.credited_seconds === body.nullifiers.length,"The credited seconds disagree with the allocation.");
  for (const id of body.nullifiers) {
    check(typeof id === "string" && digestPattern.test(id) && !seen.has(id),"A time credit is invalid or appears twice.");
    seen.add(id);
  }
}
function liveness(body,isOwner) {
  const r = body.passive_liveness;
  if (!r && isOwner) return;
  const reported = [padPolicy,singleFacePad].find(p => p.id === r?.policy_id);
  const mixed = r?.policy_id === "face-pad-mn3-window-v1-and-v2";
  check(r && (reported || mixed) && r.attestation === "registry-signed" && integer(r.screened_seconds) &&
    r.screened_seconds <= body.credited_seconds && same(Object.keys(r.windows).sort(),["inconclusive","passed","rejected"]) &&
    Object.values(r.windows).every(integer) && (!r.screened_seconds || r.windows.passed > 0),"Invalid registry-signed liveness coverage.");
  if (isOwner) {
    const parts = body.validator_policy.policies ?? [{policy:body.validator_policy,credited_seconds:body.credited_seconds}];
    const covered = mixed ? [singleFacePad,padPolicy] : [reported];
    if (mixed) check(covered.every(p=>parts.some(x=>same(x.policy,p)&&x.credited_seconds>0)),"Invalid mixed camera policy");
    check(parts.filter(x=>covered.some(p=>same(x.policy,p))).reduce((n,x)=>n+x.credited_seconds,0) === r.screened_seconds,"Liveness time differs from the signed policy allocation.");
  }
}
function field(value) { return value.toString(16).padStart(2,"0").padEnd(64,"0"); }
async function tag(parts) { return (await hashObject(parts)).slice(0,32).match(/../g).map(s => field(parseInt(s,16))); }
function estimate(runs, evidence) {
  const {prior,alpha,beta} = policy;
  const update = (p,r) => p*r/(1-p+p*r);
  const equilibrium = beta/(1-alpha+beta);
  let sum = 0;
  for (const [offset,length] of runs) {
    const forward = new Float64Array(length);
    let p = prior;
    for (let i=0;i<length;i++) {
      p = update(i ? equilibrium+(p-equilibrium)*(alpha-beta) : p,evidence.get(offset+i) ?? 1);
      forward[i] = p;
    }
    let backward = 1, subtotal = 0;
    for (let i=length-1;i>=0;i--) {
      subtotal += update(forward[i],backward);
      const factor = backward*(evidence.get(offset+i) ?? 1);
      backward = (alpha*factor+1-alpha)/(beta*factor+1-beta);
    }
    sum += subtotal;
  }
  const ms = sum*1000, floor = Math.floor(ms);
  return ms-floor === 0.5 ? floor+(floor%2) : Math.round(ms);
}
async function evidence(body, submit) {
  const activity = body.sampled_activity;
  if (activity !== undefined) {
    check(activity.scheme === "ezkl-sampled-face-edit-v1" && Array.isArray(activity.samples),"Unknown sampled activity policy.");
    const ids = new Set();
    for (const s of activity.samples) {
      check(typeof s.id === "string" && !ids.has(s.id),"Invalid or repeated activity sample.");
      ids.add(s.id);
      if (s.outcome === "positive" || s.outcome === "negative") {
        const inputs = [s.commitment,field(Number(s.outcome === "positive")),...await tag([activity.scheme,body.registry_id,body.work_id,s.id])];
        await submit("activity",s.proof,inputs);
      } else check(["interrupted","missed","proof_failed"].includes(s.outcome),"Unrecognized activity sample outcome.");
    }
  }
  const e = body.engagement;
  if (e === undefined) return {modeled:0,active:null};
  check(e.model === model && e.calibration === policy.calibration && Array.isArray(e.runs) && Array.isArray(e.classes) &&
    Array.isArray(e.positions) && Array.isArray(e.proofs) && e.positions.length === e.classes.length &&
    e.proofs.length === Math.ceil(e.classes.length/32),"Unrecognized or incomplete engagement model.");
  let end = 0, covered = 0, run = 0;
  for (const [offset,length] of e.runs) {
    check(integer(offset) && integer(length) && length > 0 && offset >= end && offset+length <= body.credited_seconds,"Invalid engagement coverage.");
    end = offset+length;
    covered += length;
  }
  const observed = new Map();
  for (const [i,position] of e.positions.entries()) {
    while (run < e.runs.length && position >= e.runs[run][0]+e.runs[run][1]) run++;
    check(integer(position) && run < e.runs.length && position >= e.runs[run][0]+4 &&
      (!i || position-e.positions[i-1]>=5) && integer(e.classes[i]) && e.classes[i]<policy.likelihood_ratios.length,"Invalid engagement observation window.");
    observed.set(position,policy.likelihood_ratios[e.classes[i]]);
  }
  const active = covered ? estimate(e.runs,observed) : null;
  check(e.modeled_seconds === covered && e.estimated_active_ms === active,"The reported engagement time differs from the recomputed estimate.");
  const scope = [model,body.registry_id,body.work_id,body.allocation_id,body.pdf_sha256,await hashObject(body.nullifiers),e.runs,e.positions];
  for (const [i,item] of e.proofs.entries()) {
    const chunk = e.classes.slice(i*32,(i+1)*32);
    while (chunk.length < 32) chunk.push(policy.classes[0]);
    await submit("engagement",item.proof,[item.commitment,...chunk.map(c=>field(c+1)),...await tag([...scope,i*32])]);
  }
  return {modeled:covered,active};
}
export async function verify(pdf,cert,trust,progress,histories=[]) {
  const p = cert?.payload;
  check(p?.kind === "attendance-allocation-v1" && p.proof_type === "ed25519-registry-receipt" && p.zero_knowledge === false,"Unsupported certificate format. Choose a Paper Presence allocation certificate.");
  check(typeof trust?.registry_id === "string" && trust.registry_id === p.registry_id,"The certificate names a different registry. Supply an independently trusted key for its issuer under Registry key.");
  await signature(trust.public_key,cert.signature,p);
  const edition = await matchPDF(pdf,cert,trust);
  check(!p.history?.length && !p.abstract_proofs?.length,"This verifier does not support historical revision-chain certificates.");
  if (p.visible_abstract) check(p.visible_abstract.policy === "poppler-cropbox-2000-tesseract-eng-page1-v1","Unknown visible abstract policy.");
  const seen = new Set();
  markers(p,seen);
  check(seen.size || p.team,"The certificate has no time allocation.");
  check(!histories.length || p.camera_audit,"No primary camera history to compare.");
  const counts = {activity:0,engagement:0,camera:0};
  if (p.camera_audit !== undefined) {
    const {verifyCamera} = await import("./camera.js");
    const known = new Map();
    counts.cameraPolicy = p.camera_audit.policy;
    counts.camera = await verifyCamera(p.camera_audit,p.work_id,trust.public_key,signature,known,p.credited_seconds);
    for (const other of histories) {
      check(other?.payload?.registry_id === trust.registry_id,"Camera comparison uses a different registry.");
      await signature(trust.public_key,other.signature,other.payload);
      await verifyCamera(other.payload.camera_audit,other.payload.work_id,trust.public_key,signature,known,other.payload.credited_seconds);
    }
  }
  async function submit(kind,proof,expected) {
    progress("Checking "+kind+" proof "+(counts[kind]+1)+"…");
    const {checkProof} = await import("./engine.bundle.js");
    await checkProof(kind,proof,expected);
    counts[kind]++;
  }
  liveness(p,true);
  let {modeled,active} = await evidence(p,submit);
  let devices = Number(seen.size > 0);
  if (p.team) {
    const t = p.team, m = t.paper.body;
    check(m.kind === "shared-paper-v1" && m.id === p.work_id && same(m.issuer,trust) && typeof m.title === "string" &&
      m.title.length > 0 && m.title.length <= 160 && typeof m.entry === "string" && !m.entry.startsWith("/") && !m.entry.includes("\\") &&
      !m.entry.split("/").includes("..") && /\.(tex|md|txt)$/i.test(m.entry),"The signed team manifest does not match this paper.");
    await signature(trust.public_key,t.paper.signature,m);
    const manifestHash = await hashObject(t.paper);
    const keys = new Set([trust.public_key]), registries = new Set([trust.registry_id]);
    for (const env of t.contributions) {
      const b = env.body, issuer = b.issuer;
      check(b.kind === "paper-contribution-v1" && b.paper === manifestHash && b.work_id === p.work_id && b.state === "ready" &&
        integer(b.sequence) && b.sequence > 0 && !keys.has(issuer.public_key) && /^[a-f0-9]{8}(?:-[a-f0-9]{4}){3}-[a-f0-9]{12}$/.test(issuer.registry_id) &&
        !registries.has(issuer.registry_id) && b.engagement && b.sampled_activity,"Invalid or repeated team contribution.");
      await signature(issuer.public_key,env.signature,b);
      keys.add(issuer.public_key); registries.add(issuer.registry_id);
      markers(b,seen); liveness(b,false);
      const e = await evidence({...b,registry_id:issuer.registry_id,allocation_id:"team-contribution-v1",pdf_sha256:b.paper},submit);
      modeled += e.modeled;
      active = modeled ? (active ?? 0)+(e.active ?? 0) : null;
      devices += Number(b.credited_seconds > 0);
    }
    check(same(t.totals,{recorded_seconds:seen.size,modeled_seconds:modeled,estimated_active_ms:active,contributor_devices:devices}),"Team totals disagree with the signed contributions.");
  }
  // Only the issuing registry has a camera report in the current certificate format.
  const auditedDevices = Number(p.credited_seconds > 0 && counts.camera > 0);
  const cameraRequirementMet = auditedDevices > 0 && auditedDevices === devices;
  return {edition,recorded:seen.size,modeled,active,devices,auditedDevices,cameraRequirementMet,counts,hash:p.pdf_sha256,registry:p.registry_id,team:Boolean(p.team)};
}
