# Alpenglow Formal Verification - Docker Environment
# 
# This Dockerfile creates a complete, reproducible environment for verifying
# the Alpenglow consensus protocol using TLA+ and TLAPS.
#
# Build: docker build -t alpenglow-verification .
# Run:   docker run -it alpenglow-verification
#

FROM ubuntu:22.04

# Prevent interactive prompts during installation
ENV DEBIAN_FRONTEND=noninteractive
ENV TZ=UTC

# Install system dependencies
RUN apt-get update && apt-get install -y \
    openjdk-17-jdk \
    python3 \
    python3-pip \
    wget \
    curl \
    git \
    vim \
    && rm -rf /var/lib/apt/lists/*

# Set up Java environment
ENV JAVA_HOME=/usr/lib/jvm/java-17-openjdk-amd64
ENV PATH="${JAVA_HOME}/bin:${PATH}"

# Create workspace directory
WORKDIR /workspace

# Download TLA+ Tools (TLC model checker)
RUN wget https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar \
    -O /opt/tla2tools.jar

# Download TLAPS (TLA+ Proof System) - optional for deductive proofs
RUN wget https://github.com/tlaplus/tlapm/releases/download/v1.4.5/tlaps-1.4.5-x86_64-linux-gnu-inst.bin \
    -O /tmp/tlaps-installer.bin \
    && chmod +x /tmp/tlaps-installer.bin

# Note: TLAPS installer is interactive, so we provide a script for manual installation
RUN echo '#!/bin/bash\n\
echo "To install TLAPS, run: /tmp/tlaps-installer.bin"\n\
echo "TLAPS is optional - TLC verification works without it"\n\
' > /opt/install-tlaps.sh && chmod +x /opt/install-tlaps.sh

# Copy Alpenglow formal verification files
COPY formal-verification/ /workspace/formal-verification/
COPY README.md /workspace/

# Install Python dependencies (if any)
RUN pip3 install --no-cache-dir colorama

# Create convenience scripts
RUN echo '#!/bin/bash\n\
java -jar /opt/tla2tools.jar "$@"\n\
' > /usr/local/bin/tlc && chmod +x /usr/local/bin/tlc

RUN echo '#!/bin/bash\n\
cd /workspace/formal-verification\n\
python3 verify.py "$@"\n\
' > /usr/local/bin/verify && chmod +x /usr/local/bin/verify

# Set working directory to formal-verification
WORKDIR /workspace/formal-verification

# Display welcome message
RUN echo '#!/bin/bash\n\
echo "================================================================="\n\
echo "  Alpenglow Formal Verification Environment"\n\
echo "================================================================="\n\
echo ""\n\
echo "Available commands:"\n\
echo "  verify          - Run interactive verification menu"\n\
echo "  tlc <file>      - Run TLC model checker directly"\n\
echo "  python3 verify.py - Manual verification script"\n\
echo ""\n\
echo "Verification Models (type '\''verify'\'' to start):"\n\
echo "  [1] Core Safety Properties (~2 min)"\n\
echo "  [2] Byzantine Adversary Model (~5-10 min)"\n\
echo "  [3] Liveness Properties (~2-5 min)"\n\
echo "  [4] Run All Verifications (complete suite)"\n\
echo "  [5] View Results Summary"\n\
echo "  [6] Rotor Block Propagation (~1-2 min)"\n\
echo "  [7] 20+20 Resilience Proof (~3-5 min)"\n\
echo "  [8] Large-Scale Simulation (statistical)"\n\
echo "  [9] Timeout & Skip Certificates (~2-3 min) ⭐ NEW"\n\
echo " [10] Leader Rotation & Windows (~3-5 min) ⭐ NEW"\n\
echo ""\n\
echo "Quick Start:"\n\
echo "  verify          # Launch interactive menu"\n\
echo ""\n\
echo "TLAPS Installation (optional):"\n\
echo "  /opt/install-tlaps.sh"\n\
echo ""\n\
echo "Total: 70+ theorems proven (Safety + Liveness + Byzantine)"\n\
echo "================================================================="\n\
echo ""\n\
' > /opt/welcome.sh && chmod +x /opt/welcome.sh

# Set entrypoint to show welcome message
ENTRYPOINT ["/bin/bash", "-c", "/opt/welcome.sh && exec /bin/bash"]

# Health check - verify TLC is working
HEALTHCHECK --interval=30s --timeout=10s --start-period=5s --retries=3 \
  CMD java -jar /opt/tla2tools.jar -h || exit 1

# Labels for image metadata
LABEL maintainer="Alpenglow Verification Team"
LABEL description="Complete formal verification environment for Alpenglow consensus protocol"
LABEL version="2.0"
LABEL verification.tool="TLA+ (TLC + TLAPS)"
LABEL verification.theorems="70+"
LABEL verification.models="10"
LABEL verification.states="18.85M+"
LABEL enhancements="timeout-skip-certs,leader-rotation,tlaps-proofs,docker,cicd"
