import {defaultTrust} from "./verify.js";

const form = document.querySelector("#verify");
const result = document.querySelector("#result");
const keyInput = document.querySelector("#key");
const sources = new Map();
let worker, controller, generation = 0;
function clear() {
  generation++;
  worker?.terminate();
  worker = null;
  controller?.abort();
  result.hidden = true;
  result.replaceChildren();
}

function createSource(id,label,accept) {
  const field = document.createElement("fieldset");
  field.innerHTML = '<legend></legend><div class="mode"><button type="button">File</button><button type="button">Link</button></div><input type="file"><input type="url" placeholder="https://…" autocomplete="off" spellcheck="false">';
  field.querySelector("legend").textContent = label;
  const [fileButton,linkButton] = field.querySelectorAll("button");
  const [file,url] = field.querySelectorAll("input");
  file.accept = accept;
  file.setAttribute("aria-label",label+" file");
  url.setAttribute("aria-label",label+" link");
  function select(link) {
    clear();
    file.hidden = file.disabled = link;
    url.hidden = url.disabled = !link;
    fileButton.setAttribute("aria-pressed",String(!link));
    linkButton.setAttribute("aria-pressed",String(link));
  }
  fileButton.onclick = () => select(false);
  linkButton.onclick = () => {select(true); url.focus();};
  select(false);
  sources.set(id,{label,file,url});
  document.querySelector("#inputs").append(field);
}
createSource("pdf","Paper PDF",".pdf,application/pdf");
createSource("certificate","Certificate",".json,application/json");
form.addEventListener("input",clear);
keyInput.onchange = () => {document.querySelector("#reset-key").hidden = !keyInput.files.length; clear();};
document.querySelector("#reset-key").onclick = () => {keyInput.value=""; keyInput.onchange();};

function directURL(input,id) {
  let url;
  try { url = new URL(input); } catch { throw Error("Enter a complete HTTPS link for the "+sources.get(id).label+"."); }
  if (url.protocol !== "https:" || url.username || url.password) throw Error("Use a public HTTPS link without login credentials.");
  const parts = url.pathname.split("/");
  if (url.hostname === "github.com" && parts[3] === "blob" && parts.length >= 6) {
    url = new URL("https://raw.githubusercontent.com/"+[parts[1],parts[2],...parts.slice(4)].join("/"));
  } else if (id === "certificate" && url.hostname === "gist.github.com" && /^\/[\w-]+\/[a-f0-9]+(?:\/[a-f0-9]+)?\/?$/.test(url.pathname)) {
    url = new URL("https://gist.githubusercontent.com/"+parts[1]+"/"+parts[2]+"/raw/"+(parts[3] ? parts[3]+"/" : "")+"certificate.json");
  }
  return url;
}
async function read(id,signal) {
  const {label,file,url} = sources.get(id);
  const max = 64*1024*1024;
  if (!file.disabled) {
    const selected = file.files[0];
    if (!selected) throw Error("Choose a "+label+" file or paste its link.");
    if (selected.size > max) throw Error(label+" exceeds the 64 MiB limit.");
    return selected.arrayBuffer();
  }
  const target = directURL(url.value.trim(),id);
  const message = "Could not download the "+label+". Use a direct link that allows browser access, or download the file and choose File.";
  let response;
  try { response = await fetch(target,{credentials:"omit",referrerPolicy:"no-referrer",signal}); }
  catch { throw Error(message); }
  if (!response.ok || !response.body) throw Error(message);
  const reader = response.body.getReader(), chunks = [];
  let size = 0;
  for (;;) {
    const {value,done} = await reader.read();
    if (done) break;
    size += value.length;
    if (size > max) { await reader.cancel(); throw Error(label+" exceeds the 64 MiB limit."); }
    chunks.push(value);
  }
  return new Blob(chunks).arrayBuffer();
}
function status(title,error=false) {
  result.replaceChildren();
  result.hidden = false;
  result.classList.toggle("error",error);
  const heading = document.createElement("h2");
  heading.textContent = title;
  result.append(heading);
}
function explain(message) {
  const p = document.createElement("p"); p.textContent = message; result.append(p);
}
function duration(ms) {
  const s = ms/1000, h = Math.floor(s/3600), m = Math.floor(s%3600/60);
  return [h ? h+" h" : "",m ? m+" min" : "",(s%60 || !h && !m) ? Number((s%60).toFixed(3))+" s" : ""].filter(Boolean).join(" ");
}
function show(r,custom,trust,requireCamera) {
  if (requireCamera && !r.cameraRequirementMet) {
    status("Camera audit requirement unmet",true);
  } else {
    status(r.cameraRequirementMet ? "PDF, certificate and sampled camera audit verified" : "PDF and registry signature verified");
  }
  explain(r.edition+" matched. The allocation signature is valid under "+(custom ? "the registry key you supplied." : "the verifier’s published registry key."));
  if (requireCamera && !r.cameraRequirementMet) {
    explain(r.team ? "Each device contributing time needs its own verified camera sample. This certificate format supports camera samples from the issuing device only." :
      "This certificate contains no verified timestamped camera windows. For a new edition, enable Paper Presence: Timestamp Camera Audit in VS Code before starting the recording.");
  }
  const dl = document.createElement("dl");
  function row(label,value,mono=false) {
    const dt=document.createElement("dt"),dd=document.createElement("dd");
    dt.textContent=label; dd.textContent=value; if (mono) dd.className="digest"; dl.append(dt,dd);
  }
  row("Registry-attested presence",duration(r.recorded*1000)+(r.team ? " across contributing devices" : ""));
  row("Timestamped camera windows verified",String(r.counts.camera));
  row("Contributing devices with verified samples",r.auditedDevices+" of "+r.devices);
  row("Estimated engagement",r.active === null ? "No modeled time in this certificate" : duration(r.active)+" across "+duration(r.modeled*1000)+" of modeled presence");
  if (r.counts.camera) row("What the sample proves",r.counts.cameraPolicy==="camera-minute-3-yunet-output-maps-v1" ? "At least one qualifying face in each of three committed YuNet output maps per window. Image-to-map inference and liveness rely on the recorder." : "The private-pixel classifier ran on the three frames in each disclosed window.");
  row("Zero-knowledge proofs",r.counts.activity+r.counts.engagement || r.counts.camera ? r.counts.activity+" activity and "+r.counts.engagement+" engagement proofs verified"+(r.counts.camera ? ", "+r.counts.camera+" camera proofs verified" : "") : "No embedded proofs in this allocation");
  row("Certified PDF SHA-256",r.hash,true);
  row("Registry ID",r.registry,true);
  row("Registry public key",trust.public_key,true);
  result.append(dl); result.focus();
}
form.addEventListener("submit",async event => {
  event.preventDefault(); clear();
  const current = generation;
  const requireCamera = document.querySelector("#require-camera").checked;
  controller = new AbortController();
  status("Reading files…");
  function fail(message) {
    if (current !== generation) return;
    controller.abort(); worker?.terminate(); worker=null;
    status("Verification incomplete",true); explain(message); result.focus();
  }
  try {
    const custom = keyInput.files[0];
    if (custom?.size > 8192) throw Error("Choose a small registry public key JSON file.");
    let trust = defaultTrust;
    if (custom) {
      try {
        const key = JSON.parse(await custom.text());
        if (typeof key.registry_id !== "string" || typeof key.public_key !== "string" || !/^[a-f0-9]{64}$/.test(key.public_key)) throw Error();
        trust = {registry_id:key.registry_id,public_key:key.public_key};
      } catch { throw Error("The registry key must contain a registry_id and a 32-byte hexadecimal public_key."); }
    }
    const [pdf,certificate] = await Promise.all([read("pdf",controller.signal),read("certificate",controller.signal)]);
    if (current !== generation) return;
    status("Checking signature and PDF…");
    worker = new Worker(new URL("./worker.js",import.meta.url),{type:"module"});
    worker.onmessage = ({data}) => {
      if (current !== generation) return;
      if (data.progress) status(data.progress);
      else if (data.error) fail(data.error);
      else {worker.terminate(); worker=null; show(data.result,custom,trust,requireCamera);}
    };
    worker.onerror = () => fail("The verification engine could not run in this browser. Reload the page or try a current browser.");
    const files = [...document.querySelector("#camera-history").files];
    if (files.reduce((n,f)=>n+f.size,0)>64*1024*1024) throw Error("Additional certificates exceed 64 MiB.");
    const histories = await Promise.all(files.map(f=>f.arrayBuffer()));
    if (current !== generation) return;
    worker.postMessage({pdf,certificate,trust,histories},[pdf,certificate,...histories]);
  } catch (err) {fail(err.message);}
});
