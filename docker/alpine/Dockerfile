FROM alpine:edge

RUN apk --update add alpine-sdk grep bash

RUN addgroup -g 1000 user \
  && adduser -D -h /home/user -G user -u 1000 user \
  && addgroup user abuild

USER user
ENV HOME /home/user
