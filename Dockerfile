
FROM python:3.12-slim

ENV DEBIAN_FRONTEND=noninteractive \
    PIP_NO_CACHE_DIR=1 \
    PYTHONDONTWRITEBYTECODE=1 \
    PYTHONUNBUFFERED=1 \
    OQS_INSTALL_PATH=/usr/local \
    LD_LIBRARY_PATH=/usr/local/lib:${LD_LIBRARY_PATH}

# ------------------------------------------------------------
# System deps
# ------------------------------------------------------------
RUN apt-get update && apt-get install -y --no-install-recommends \
    ca-certificates \
    curl \
    cmake \
    ninja-build \
    build-essential \
    pkg-config \
 && rm -rf /var/lib/apt/lists/*

WORKDIR /app

# ------------------------------------------------------------
# PQ provenance inputs
# ------------------------------------------------------------
COPY lock.manifest.json lock.manifest.pqsig pq_pubkey.b64 requirements.txt ./

# ------------------------------------------------------------
# Build liboqs (C) with SHA256 pin
# ------------------------------------------------------------
ARG LIBOQS_VERSION=0.14.0
ARG LIBOQS_TARBALL_SHA256=5b0df6138763b3fc4e385d58dbb2ee7c7c508a64a413d76a917529e3a9a207ea

RUN set -euo pipefail \
 && curl -fsSL -o /tmp/liboqs.tar.gz \
      "https://github.com/open-quantum-safe/liboqs/archive/refs/tags/${LIBOQS_VERSION}.tar.gz" \
 && echo "${LIBOQS_TARBALL_SHA256}  /tmp/liboqs.tar.gz" | sha256sum -c - \
 && mkdir -p /tmp/liboqs-src \
 && tar -xzf /tmp/liboqs.tar.gz -C /tmp/liboqs-src --strip-components=1 \
 && cmake -S /tmp/liboqs-src -B /tmp/liboqs-src/build \
      -DCMAKE_INSTALL_PREFIX=/usr/local \
      -DBUILD_SHARED_LIBS=ON \
      -DOQS_USE_OPENSSL=OFF \
      -DCMAKE_POSITION_INDEPENDENT_CODE=ON \
      -G Ninja \
 && cmake --build /tmp/liboqs-src/build --parallel \
 && cmake --install /tmp/liboqs-src/build \
 && ldconfig \
 && rm -rf /tmp/liboqs.tar.gz /tmp/liboqs-src

# ------------------------------------------------------------
# Bootstrap minimal Python for PQ verification
# (avoid brittle hash lists for verifier deps)
# ------------------------------------------------------------
RUN python -m pip install --upgrade pip

# Install verifier tool only (no dependency resolution here).
# Application dependencies remain hash-locked later via requirements.txt.
RUN set -euo pipefail \
 && python -m pip install --no-cache-dir --no-deps \
    liboqs-python==0.14.1

# ------------------------------------------------------------
# PQ authenticity verification (Dilithium)
# ------------------------------------------------------------
RUN python <<'PY'
import base64, hashlib, json, sys, pathlib
import oqs

manifest = pathlib.Path("lock.manifest.json")
sig = pathlib.Path("lock.manifest.pqsig")
pub = pathlib.Path("pq_pubkey.b64")
req = pathlib.Path("requirements.txt")

for p in (manifest, sig, pub, req):
    if not p.exists():
        print(f"ERROR: missing required file: {p}", file=sys.stderr)
        sys.exit(2)

msg = manifest.read_bytes()
signature = base64.b64decode(sig.read_text().strip())
pubkey = base64.b64decode(pub.read_text().strip())

alg = "Dilithium2"
with oqs.Signature(alg) as v:
    if not v.verify(msg, signature, pubkey):
        print("ERROR: PQ signature verification FAILED for lock.manifest.json", file=sys.stderr)
        sys.exit(3)

m = json.loads(msg.decode("utf-8"))
expected = (m.get("requirements_txt_sha256") or "").lower().strip()
if not expected or len(expected) != 64:
    print("ERROR: manifest missing requirements_txt_sha256", file=sys.stderr)
    sys.exit(4)

actual = hashlib.sha256(req.read_bytes()).hexdigest().lower()
if actual != expected:
    print("ERROR: requirements.txt SHA256 mismatch", file=sys.stderr)
    print(f" expected: {expected}", file=sys.stderr)
    print(f"   actual: {actual}", file=sys.stderr)
    sys.exit(5)

print("OK: PQ signature + requirements.txt SHA256 verified.")
PY

# ------------------------------------------------------------
# Install full dependency graph (hash locked)
# ------------------------------------------------------------
RUN python -m pip install --no-cache-dir --require-hashes -r requirements.txt

# ------------------------------------------------------------
# App
# ------------------------------------------------------------
COPY . .

RUN useradd -ms /bin/bash appuser \
 && mkdir -p /app/static \
 && chmod 755 /app/static \
 && chown -R appuser:appuser /app

USER appuser

EXPOSE 3000

CMD ["gunicorn","main:app","-b","0.0.0.0:3000","-w","4","-k","gthread","--threads","4","--timeout","180","--graceful-timeout","30","--log-level","info","--preload","--max-requests","1000","--max-requests-jitter","200"]
```0
