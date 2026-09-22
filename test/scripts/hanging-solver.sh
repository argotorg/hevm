#!/usr/bin/env sh
# Fake SMT solver for tests: acks every command and never answers (check-sat), unless the query set :status unsat
exec awk '
  /\(set-info :status unsat\)/ { unsat = 1 }
  { depth += gsub(/\(/, "(") - gsub(/\)/, ")") }
  depth != 0 { next }
  /\(check-sat\)/ {
    if (unsat) { print "unsat"; fflush(); next }
    while ((getline line) > 0) {}
    exit
  }
  { print "success"; fflush() }
'
