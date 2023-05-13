# Base image
FROM docker.io/eclipse-temurin:17-jre

# Get dependencies of npm
RUN apt-get update && \
    apt-get install -y wget opam libgmp-dev && \
    rm -rf /var/lib/apt/lists/*

RUN opam init --disable-sandboxing && \
    opam repo add coq-released https://coq.inria.fr/opam/released
ENV COQ_VERSION 8.16.1
RUN opam pin add coq "$COQ_VERSION" -y
ENV COQ_EQUATIONS_VERSION 1.3+8.16
RUN opam pin add coq-equations "$COQ_EQUATIONS_VERSION" -y

# Install scala and sbt
ENV SCALA_VERSION 3.2.2
ENV SBT_VERSION 1.8.2
RUN cd /tmp && \
    wget -q "https://github.com/lampepfl/dotty/releases/download/${SCALA_VERSION}/scala3-${SCALA_VERSION}.tar.gz" -O - | tar xz && \
    mkdir "/usr/share/scala" && \
    mv "/tmp/scala3-${SCALA_VERSION}/bin" "/tmp/scala3-${SCALA_VERSION}/lib" "/usr/share/scala" && \
    ln -s "/usr/share/scala/bin/"* "/usr/bin/" && \
    wget -q "https://github.com/sbt/sbt/releases/download/v${SBT_VERSION}/sbt-${SBT_VERSION}.tgz" -O - | tar xz && \
    mv "/tmp/sbt/bin/"* "/usr/bin"

# Do one temporary compilation to get dependencies
RUN mkdir /tmp/src
COPY ./ /tmp/src/
RUN cd /tmp/src && \
    sh "run.sh" && \
    rm -r /tmp/src

# TODO anything to apt-get remove to save space?
#RUN apt-get remove -y g++ make python3 && \
#    apt-get -y clean autoclean && \
#    apt-get -y autoremove

# move into the directory to be mapped by -v
WORKDIR /app

# Execute
CMD ["sh", "run.sh"]
