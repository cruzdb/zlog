#!/bin/bash
set -e
set -x

CLI_CMD=zlog
LMDB_DIR=$(mktemp -d)

INPUT_FILE=$(mktemp)
OUTPUT_FILE=$(mktemp)
EXPECTED_FILE=$(mktemp)
trap "rm -rf ${LMDB_DIR} ${INPUT_FILE} ${OUTPUT_FILE} ${EXPECTED_FILE}" exit

${CLI_CMD} --backend lmdb --db-path ${LMDB_DIR} log create testlog 
! ${CLI_CMD} --backend lmdb --db-path ${LMDB_DIR} log create testlog 

${CLI_CMD} --backend lmdb --db-path ${LMDB_DIR} log append testlog 'just a lil test'
${CLI_CMD} --backend lmdb --db-path ${LMDB_DIR} log append testlog 'and another'
${CLI_CMD} --backend lmdb --db-path ${LMDB_DIR} log append testlog 'one more and were done'

echo '616e6420616e6f74686572' >> ${EXPECTED_FILE}
${CLI_CMD} --backend lmdb --db-path ${LMDB_DIR} log read testlog 1 >> ${OUTPUT_FILE}
diff ${EXPECTED_FILE} ${OUTPUT_FILE}

> ${EXPECTED_FILE}
> ${OUTPUT_FILE}

echo 'arthur willey!' >> ${INPUT_FILE}
echo 'nautili hunter' >> ${INPUT_FILE}
echo 'abcdefghijlmno' >> ${INPUT_FILE}

${CLI_CMD} --backend lmdb --db-path ${LMDB_DIR} log append testlog -i ${INPUT_FILE}

echo '0: 6a7573742061206c696c2074657374' >> ${EXPECTED_FILE}
echo '1: 616e6420616e6f74686572' >> ${EXPECTED_FILE}
echo '2: 6f6e65206d6f726520616e64207765726520646f6e65' >> ${EXPECTED_FILE}
echo '3: 6172746875722077696c6c6579210a6e617574696c692068756e7465720a6162636465666768696a6c6d6e6f0a' >> ${EXPECTED_FILE}

${CLI_CMD} --backend lmdb --db-path ${LMDB_DIR} log dump testlog >> ${OUTPUT_FILE}

diff ${EXPECTED_FILE} ${OUTPUT_FILE}

${CLI_CMD} --backend lmdb --db-path ${LMDB_DIR} log fill testlog 30
! ${CLI_CMD} --backend lmdb --db-path ${LMDB_DIR} log fill testlog 1

${CLI_CMD} --backend lmdb --db-path ${LMDB_DIR} log trim testlog 2

