#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/../.."
python3 -m compileall -q deploy
for file in deploy/*.js; do
  node --check "$file"
done
python3 -B -m unittest \
  deploy.test_zhihu \
  deploy.test_github_identity \
  deploy.test_presence \
  deploy.test_desk \
  deploy.test_agent_attribution \
  deploy.test_desk_scale.DeskScaleTest.test_agent_attribution_across_problem_desks \
  deploy.test_desk_scale.DeskScaleTest.test_directory_counts_and_scoped_join_guides \
  deploy.test_desk_scale.DeskScaleTest.test_verification_history_pagination \
  deploy.test_rankings \
  deploy.test_landau \
  deploy.test_publish_catalogue \
  research.test_catalogue
