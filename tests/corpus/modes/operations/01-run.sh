#!/bin/sh
# Publish the journal.
rsync -a entries/ "$1"
