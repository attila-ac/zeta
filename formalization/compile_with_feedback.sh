#!/bin/bash
FILENAME=$1

# coqc -Q . Formalization trigonometric_exponential_constants.v

# Compile the Coq file with the namespace mapping
if coqc -Q . Formalization "$FILENAME"; then
    echo "Successfully compiled $FILENAME"
else
    echo "Failed to compile $FILENAME"
fi

