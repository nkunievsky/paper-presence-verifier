# Paper Presence verifier

[Open the public verifier](https://nkunievsky.github.io/paper-presence-verifier/).

Choose the paper PDF and its Paper Presence certificate independently. Each input accepts a local file or a direct HTTPS link, up to 64 MiB. Verification runs in a web worker. Local files stay on the device. For a link, the browser downloads the file directly from its host, which must permit cross-origin access. GitHub file links and the extension’s certificate Gist links are supported.

## What the result covers

The public form requires a verified timestamped camera sample from every device claiming time by default. The result shows the registry-attested duration, verified window count, and number of contributing devices with verified samples. The current team format carries only the issuing device’s camera report. To inspect older receipts or a team allocation with unsampled contributors, clear the requirement. All attached proofs still undergo verification in either mode. Windows describe the disclosed recording runs. The certificate does not link individual credited seconds to those windows.

- The verifier checks the Ed25519 allocation signature against the pinned public registry key. Other issuers require a key obtained independently, selected under **Registry key**. An author-supplied key authenticates a signature only to the extent the reader trusts that key.
- The PDF’s SHA-256 must match the signed allocation. For an extension-generated publication copy, the verifier additionally checks its signed trailer, the original bytes, the annotated body, and the digest of the accompanying certificate. Reprinting or rebuilding a PDF can change its bytes.
- Recorded time is checked against unique allocated seconds within the certificate. Team receipts also require the signed paper manifest, independently signed contributions scoped to that manifest, unique device keys and credits, and exact aggregate totals. The device count does not identify distinct people. The verifier has no global database of other certificates.
- Where present, all sampled face/edit and engagement-classification proofs are verified against the two fixed EZKL 23.0.5 circuits and the expected public inputs for the paper and observations. The worker executes their Solidity verification bytecode locally using EthereumJS. No blockchain, wallet, RPC, or transaction is involved.
- The worker reruns the Bayesian smoother and compares the estimated milliseconds and coverage to the receipt. A receipt with no embedded proofs says so. Interrupted or missed samples do not count as proofs. Passive liveness is a registry attestation. Physical presence, attention, and authorship depend on the capture process and model.
- Historical revision-chain certificates are unsupported and return an incomplete result.

## Trust anchor

The default registry ID is `94293088-5a7f-436b-8644-b5bf61d0bf8f`. Its Ed25519 public key in hexadecimal is `5609e907aac6e9feede098da7a54c7670eb381eb35125ebf98869d4d8fafcb12`. Compare it with a trusted copy of the issuer’s public key. Local registry secrets are never needed.

## Serving and rebuilding

Serve the repository using GitHub Pages, or run `python3 -m http.server` from its root and open localhost in a browser supporting Web Crypto Ed25519 and module workers. The committed assets are ready to serve.

The two contracts in `circuits/` were generated from the Paper Presence activity and engagement verification keys, settings, and public KZG SRS with EZKL 23.0.5 using `create_evm_verifier(..., reusable=False)`. Their checked-in binaries are the optimized runtime bytecode from solc 0.8.27, compiled with the source filenames `zkdata.sol` and `hmmdata.sol` respectively. Each exposes `verifyProof(bytes,uint256[])`.

To rebuild the browser engine with Node 22, run the following commands in `build/`.

```sh
npm ci
npm run bundle
```

The engine uses EthereumJS and its dependencies. The lockfile records the exact upstream sources and package integrity hashes. Distribution notices are in [Third-party notices](THIRD_PARTY.md).

## Experimental timestamped camera audit

For 0.7.9 first-edition certificates, the worker also checks the exact RFC 3161 request imprint, nonce, accepted policy, signed time, timestamp-signing EKU and signature chain to the FreeTSA root bundled in this verifier. It verifies each three-frame UltraHonk proof using a fixed verifier compiled by Barretenberg 6.0.0. Additional signed certificates selected under **Compare camera histories** share a credential-and-minute index during verification. There is no external lookup for omitted records. Verification uses the shipped static assets and opens no timestamp-service connection.

Reproduce the camera verifier from the repository root with the project's Barretenberg binary, then solc 0.8.27. Convert the hexadecimal runtime in `HonkVerifier.bin-runtime` into raw bytes for `circuits/camera.bin`. The browser PKI bundle incorporates the project's pinned FreeTSA root from `prototype/timestamp_trust`.

```sh
bb write_solidity_verifier -k presence-0.7/experiments/presence_proof/window_key.key -o /tmp/camera.sol -t evm --optimized
solc --optimize --bin-runtime /tmp/camera.sol -o /tmp/camera-runtime
```

New 0.7.10 camera windows use an embedded RISC Zero composite receipt. The worker verifies it with the shipped WebAssembly module and fixed guest image ID, and compares its 32-byte journal with the timed, signed window commitment. A positive proof covers the YuNet detection rule on each of three private output maps. Image-to-map inference, camera origin and liveness rely on the recording installation.
