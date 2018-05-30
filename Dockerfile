FROM fpco/stack-build:lts-11.10
RUN mkdir /opt/strictcheck
COPY . /opt/strictcheck
RUN cd /opt/strictcheck && stack haddock

ENTRYPOINT ["/bin/bash"]
