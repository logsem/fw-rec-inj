FROM coqorg/coq:8.16.1
WORKDIR /home/coq/artifact
COPY . .
RUN sudo chown -R coq:coq ./