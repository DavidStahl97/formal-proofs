FROM ubuntu:20.04

RUN apt update
RUN apt install -y agda-bin=2.6.0.1-1build4