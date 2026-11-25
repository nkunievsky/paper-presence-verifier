import {verify} from "./verify.js";
self.onmessage = async ({data}) => {
  try {
    const result = await verify(new Uint8Array(data.pdf),JSON.parse(new TextDecoder("utf-8",{fatal:true}).decode(data.certificate)),data.trust,
      progress => self.postMessage({progress}));
    self.postMessage({result});
  } catch (err) {
    const error = err instanceof SyntaxError ? "The certificate or signed publication trailer is not valid JSON." :
      err instanceof TypeError ? "The certificate is incomplete or has malformed fields." : err.message;
    self.postMessage({error});
  }
};
