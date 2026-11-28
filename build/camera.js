import {Certificate, SignedData, TimeStampReq, TimeStampResp, TSTInfo} from "pkijs";
import {fromBER} from "asn1js";
import rootPEM from "./freetsa-root.pem";

const bytes = b64 => Uint8Array.from(atob(b64), c => c.charCodeAt(0));
const hex = data => Array.from(new Uint8Array(data), b => b.toString(16).padStart(2,"0")).join("");
const oidSHA256 = "2.16.840.1.101.3.4.2.1";
const oidTimestamp = "1.2.840.113549.1.9.16.1.4";

function requireValue(ok) {
  if (!ok) throw Error("Invalid FreeTSA camera timestamp.");
}
function parse(type, data) {
  requireValue(data.length > 0 && data.length <= 1048576);
  const parsed = fromBER(data);
  requireValue(parsed.offset === data.length);
  return new type({schema:parsed.result});
}

export async function cameraTimestamp(entryBytes, item) {
  const request = parse(TimeStampReq,bytes(item.request));
  const response = parse(TimeStampResp,bytes(item.response));
  requireValue(request.version === 1 && request.nonce && request.reqPolicy === "1.2.3.4.1" &&
    [0,1].includes(response.status.status) && response.timeStampToken?.contentType === "1.2.840.113549.1.7.2");
  const signed = new SignedData({schema:response.timeStampToken.content});
  requireValue(signed.signerInfos.length === 1 && signed.encapContentInfo.eContentType === oidTimestamp);
  const info = parse(TSTInfo,signed.encapContentInfo.eContent.valueBlock.valueHexView);
  const digest = hex(await crypto.subtle.digest("SHA-256",entryBytes));
  requireValue(info.version === 1 && info.policy === request.reqPolicy && info.nonce?.isEqual(request.nonce));
  for (const imprint of [request.messageImprint,info.messageImprint])
    requireValue(imprint.hashAlgorithm.algorithmId === oidSHA256 && hex(imprint.hashedMessage.valueBlock.valueHexView) === digest);
  const root = parse(Certificate,bytes(rootPEM.replace(/-----[^-]+-----|\s/g,"")));
  const result = await signed.verify({signer:0,checkChain:true,trustedCerts:[root],data:entryBytes,extendedMode:true});
  const signer = result.signerCertificate;
  const eku = signer?.extensions?.find(e => e.extnID === "2.5.29.37");
  requireValue(result.signatureVerified === true && result.signerCertificateVerified === true &&
    eku?.critical && eku.parsedValue?.keyPurposes?.length === 1 && eku.parsedValue.keyPurposes[0] === "1.3.6.1.5.5.7.3.8");
  return info.genTime.getTime();
}
