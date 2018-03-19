#! /usr/bin/env bash

# Copy doc/html to Google Cloud bucket cprover.diffblue.com

set -euo pipefail


#### Variables

#User-defined variables
DOCS_FQDN="cprover.diffblue.com"
DOCS_GS="gs://${DOCS_FQDN}"

# Path to generated HTML documentation
DOCS_PATH="$(dirname "$(readlink -f "$0")")/../doc/html"

# Colors for nice output
GREEN='\033[0;32m'
#RED='\033[0;31m'
NC='\033[0m' # No Color


#### Deployments

# For develop branch
if [[ "${BRANCH:-null}" == "develop" ]]; then

  echo -e "\n${GREEN}Uploading ${DOCS_FQDN}${NC}\n"
  # Copy HTML docs to gcloud
  gsutil -m -h "Cache-Control:public,max-age=60" \
    rsync -r -d -c "${DOCS_PATH}" "${DOCS_GS}/"
  echo -e "\n${GREEN}${DOCS_FQDN} is live${NC}\n"

# For all other branches
else
  echo -e "\n${GREEN}Nothing to upload in >>${BRANCH}<< branch.${NC}\n"
fi
