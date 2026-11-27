"""Submission provenance is self-reported, immutable and tied to an authorized head."""
import json
import re
import sqlite3
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from deploy.desk import Desk, HARNESS_NAMES, agent_metadata, model_ranking_name
from deploy import test_desk as desk_tests
from deploy.test_desk import GAPS, START
from tools import goldbach


class AttributionTests(unittest.TestCase):
    def setUp(self):
        self.helper = desk_tests.DeskTests()
        self.helper.setUp()
        self.addCleanup(self.helper.doCleanups)
        self.desk = self.helper.desk
        self.agent = dict(model='Model-A-2026', harness='codex', harness_version='1.2.3')

    def submit(self, token, agent=None, **options):
        body = dict(pr=8, head='a' * 40)
        body.update(options)
        if agent is not None:
            body['agent'] = agent
        return self.helper.request('submit', body, token=token)

    def test_validation_and_normalization(self):
        self.assertEqual(agent_metadata(self.agent)['model'], 'model-a-2026')
        self.assertEqual(agent_metadata({'model': 'MODEL  A', 'harness': 'CODEX'})['model'], 'model a')
        for value in ([], 'codex', {'model': ''}, {'model': True}, {'model': 'a'*97},
                      {'model': '<script>'}, {'model': 'a\nb'}, {'harness': 'made-up'}, {'extra': 1}):
            with self.subTest(value=value), self.assertRaises(ValueError):
                agent_metadata(value)
        token = self.helper.claim()
        self.assertEqual(self.submit(token, {'harness': 'made-up'})[0], 400)
        self.assertEqual(self.submit(token, self.agent)[0], 200)

    def test_harness_catalogue_matches_cli_display_and_guides(self):
        root = Path(__file__).resolve().parents[1]
        self.assertEqual(set(HARNESS_NAMES), set(goldbach.HARNESS_NAMES))
        source = (root / 'deploy/site.js').read_text()
        labels = json.loads(re.search(r'const harnessLabels = (\{.*?\});', source, re.S)[1])
        self.assertEqual(set(labels), set(HARNESS_NAMES) - {'other', 'unknown'})
        for harness in HARNESS_NAMES:
            with self.subTest(harness=harness):
                self.assertEqual(agent_metadata({'model': 'new-model-v1', 'harness': harness})['harness'], harness)
                for guide in ('deploy/join.txt', 'deploy/join-zh.txt', 'CONTRIBUTING.md'):
                    self.assertIn(harness, (root / guide).read_text())
        self.assertEqual(labels['kimi-code'], 'Kimi Code')
        with self.assertRaises(ValueError):
            agent_metadata({'model': 'kimi-k2', 'harness': 'made-up'})

    def test_model_effort_aliases_do_not_merge_versions_or_other_models(self):
        for label in ('gpt-6.2-astra', 'gpt-6.2 astra high', '6.2 astrahigh',
                      'GPT-6.2-ASTRA-XHIGH', 'openai/gpt-6.2-astra-medium'):
            self.assertEqual(model_ranking_name(label), 'gpt-6.2-astra')
        for label in ('gpt-6.1-astra', 'gpt-6.2-sol', 'gpt-6.2-astra-preview',
                      'custom/gpt-6.2-astra-high', 'deepseek-v4.1-flash',
                      'qwen3-max', 'claude-opus-high', 'kimi-k2', 'new-model-v1'):
            self.assertEqual(model_ranking_name(label), label)

    def test_model_aliases_aggregate_only_winners_and_preserve_provenance(self):
        rows = [('gpt-6.2-astra', 'codex')] * 17 + [('gpt-6.2 astra high', 'kimi-code')] * 9
        rows += [('gpt-6.2-sol', 'qwen-code'), ('gpt-6.1-astra', 'other')]
        with self.desk.transaction(write=True) as conn:
            for run, (model, harness) in enumerate(rows, 1):
                conn.execute("""INSERT INTO goldbach_leases
                    (token_hash,gap,statement_sha256,handle,ip_key,claimed_at,expires_at,
                     absolute_expires_at,pr,head,run_id,finished_at,verdict,model,harness,agent_reported)
                    VALUES (?,?,'hash','alice','network',0,0,0,?,'head',?,?,'ACCEPTED',?,?,1)
                """, (str(run), f'lemma-{run}', run, run, START+run, model, harness))
            # A later proof of the same lemma cannot acquire another count through an alias.
            conn.execute("""INSERT INTO goldbach_leases
                (token_hash,gap,statement_sha256,handle,ip_key,claimed_at,expires_at,
                 absolute_expires_at,run_id,finished_at,verdict,model,harness)
                VALUES ('later','lemma-1','hash','bob','network',0,0,0,99,?,
                        'ACCEPTED','6.2 astrahigh','cline')""", (START+99,))
        ranks = self.helper.status(now=START+100)['agent_rankings']
        self.assertEqual(ranks['models'], [
            {'name': 'gpt-6.2-astra', 'accepted': 26, 'points': 26},
            {'name': 'gpt-6.1-astra', 'accepted': 1, 'points': 1},
            {'name': 'gpt-6.2-sol', 'accepted': 1, 'points': 1},
        ])
        self.assertEqual(ranks['harnesses'], [
            {'name': 'codex', 'accepted': 17, 'points': 17}, {'name': 'kimi-code', 'accepted': 9, 'points': 9},
            {'name': 'other', 'accepted': 1, 'points': 1}, {'name': 'qwen-code', 'accepted': 1, 'points': 1},
        ])
        self.assertEqual(ranks['proofs'], 28)
        records = [{'run_id': 18, 'lemma_id': 'lemma-18'}]
        with self.desk.transaction() as conn:
            self.desk.annotate_verdicts(records, conn)
        self.assertEqual(records[0]['agent']['model'], 'gpt-6.2 astra high')

    def test_ranking_alias_does_not_change_frozen_retry_metadata(self):
        token = self.helper.claim()
        agent = dict(self.agent, model='gpt-6.2 astra high', harness='kimi-code')
        self.assertEqual(self.submit(token, agent)[0], 200)
        self.assertEqual(self.submit(token, agent)[0], 200)
        self.assertEqual(self.submit(token, dict(agent, model='gpt-6.2-astra')),
                         (409, {'error': 'submission_metadata_frozen'}))

    def test_new_submissions_require_both_fields_without_consuming_lease(self):
        token = self.helper.claim()
        for fields in ({}, {"agent": None}, {"agent": {}}, {"agent": {"model": "a"}},
                       {"agent": {"harness": "codex"}}):
            body = {"pr": 8, "head": "a"*40, **fields}
            self.assertEqual(self.helper.request("submit", body, token=token),
                             (400, {"error": "agent_model_and_harness_required"}))
        self.assertEqual(self.submit(token, {"model": "model-a", "harness": "codex"})[0], 200)

    def test_metadata_frozen_and_legacy_retry_does_not_erase_it(self):
        token = self.helper.claim()
        self.assertEqual(self.submit(token, self.agent)[0], 200)
        self.assertEqual(self.submit(token, self.agent)[0], 200)
        self.assertEqual(self.submit(token)[0], 200)
        self.assertEqual(self.submit(token, dict(self.agent, model='model-b')),
                         (409, {'error': 'submission_metadata_frozen'}))
        self.assertEqual(self.submit(token, self.agent, head='b'*40)[0], 409)
        with self.desk.transaction() as conn:
            row = conn.execute('SELECT model, harness, harness_version FROM goldbach_leases').fetchone()
        self.assertEqual(tuple(row), ('model-a-2026', 'codex', '1.2.3'))

    def test_changed_head_keeps_its_own_attribution_and_authorized_run(self):
        token = self.helper.claim()
        self.submit(token, self.agent)
        self.assertEqual(self.helper.request('authorize', self.helper.authorization(), sign=True)[0], 200)
        with patch('deploy.desk.time.time', return_value=START+10):
            self.helper.record(102, GAPS[0]['id'], 'REJECTED')
        token2 = self.helper.claim(now=START+20)
        self.assertEqual(self.submit(token2, dict(self.agent, model='model-b'), head='b'*40)[0], 200)
        self.assertEqual(self.helper.request('authorize', self.helper.authorization(head='a'*40, run_id=103), sign=True)[0], 409)
        self.assertEqual(self.helper.request('authorize', self.helper.authorization(head='b'*40, run_id=103), sign=True)[0], 200)
        with patch('deploy.desk.time.time', return_value=START+30):
            self.helper.record(103, GAPS[0]['id'], 'ACCEPTED')
            self.helper.record(103, GAPS[0]['id'], 'ACCEPTED', attempt=2)
            self.helper.record(103, GAPS[0]['id'], 'REJECTED', attempt=3)
        records = [{'run_id': 102, 'lemma_id': GAPS[0]['id']}, {'run_id': 103, 'lemma_id': GAPS[0]['id']}, {'run_id': 103, 'lemma_id': GAPS[1]['id']}]
        with self.desk.transaction() as conn:
            self.desk.annotate_verdicts(records, conn)
        self.assertEqual([r['agent']['model'] for r in records], ['model-a-2026', 'model-b', 'unknown'])
        self.assertEqual(records[0]['agent']['source'], 'self_reported')
        ranks = self.helper.status(now=START+40)['agent_rankings']
        self.assertEqual(ranks, {'models': [{'name': 'model-b', 'accepted': 1, 'points': 1}], 'harnesses': [{'name': 'codex', 'accepted': 1, 'points': 1}], 'proofs': 1})

    def test_first_acceptance_unknown_history_and_separate_models(self):
        with self.desk.transaction(write=True) as conn:
            for run, gap, model, harness, verdict in [
                (1, 'first', 'model-a', 'codex', 'ACCEPTED'),
                (2, 'first', 'model-b', 'cursor', 'ACCEPTED'),
                (3, 'second', 'model-a-v2', 'codex', 'ACCEPTED'),
                (4, 'third', 'unknown', 'unknown', 'ACCEPTED'),
                (6, 'fifth', 'model-c', 'unknown', 'ACCEPTED'),
                (7, 'sixth', 'unknown', 'cursor', 'ACCEPTED'),
                (5, 'fourth', 'model-b', 'cursor', 'REJECTED'),
            ]:
                conn.execute("""INSERT INTO goldbach_leases (token_hash,gap,statement_sha256,handle,ip_key,claimed_at,expires_at,absolute_expires_at,run_id,finished_at,verdict,model,harness)
                    VALUES (?,?,'hash','alice','network',0,0,0,?,?,?,?,?)""", (str(run),gap,run,START+run,verdict,model,harness))
        status = self.helper.status(now=START+20)
        ranks = status['agent_rankings']
        self.assertEqual(ranks['proofs'], 4)
        self.assertEqual(status['rankings']['proofs'], 5)
        self.assertEqual(ranks['models'], [{'name': x, 'accepted': 1, 'points': 1} for x in ['model-a', 'model-a-v2', 'model-c']])
        self.assertEqual(ranks['harnesses'], [{'name': 'codex', 'accepted': 2, 'points': 2}, {'name': 'cursor', 'accepted': 1, 'points': 1}])
        self.assertNotIn('ip_key', json.dumps(status))
        self.assertNotIn('token_hash', json.dumps(status))

    def test_additive_migration_and_missing_metadata(self):
        token = self.helper.claim()
        self.assertEqual(self.submit(token, self.agent)[0], 200)
        with sqlite3.connect(self.helper.db) as conn:
            for column in ('model', 'harness', 'harness_version', 'agent_reported'):
                conn.execute(f'ALTER TABLE goldbach_leases DROP COLUMN {column}')
        for _ in range(2):
            migrated = Desk(self.helper.db, GAPS, b'test-secret')
            with migrated.transaction() as conn:
                row = conn.execute('SELECT model,harness,harness_version,agent_reported,pr,head FROM goldbach_leases').fetchone()
            self.assertEqual(tuple(row), ('unknown', 'unknown', 'unknown', 0, 8, 'a'*40))
        self.assertEqual(self.submit(token)[0], 200)


class SubmissionToolTests(unittest.TestCase):
    def setUp(self):
        folder = self.enterContext(tempfile.TemporaryDirectory())
        self.path = Path(folder)/'lease.json'
        self.state = dict(branch='task-branch', handle='alice', base='c'*40, token='private-lease', gap=dict(id='L-goldbach-test', file='lean/PEqualNP/Outside/Test.lean'))
        self.agent = dict(model='model-a', harness='codex', harness_version='unknown')
        pr = dict(state='open', user={'login':'alice'}, head={'sha':'a'*40}, base={'ref':'main','repo':{'full_name':goldbach.REPO,'default_branch':'main'}}, changed_files=1)
        self.command = self.enterContext(patch.object(goldbach, 'command', side_effect=lambda *args: json.dumps(pr) if args[:2]==('gh','api') else ('a'*40 if args[:2]==('git','rev-parse') else '')))
        self.enterContext(patch.object(goldbach,'current_branch',return_value='task-branch'))
        self.enterContext(patch.object(goldbach,'authenticated_login',return_value='alice'))
        self.enterContext(patch.object(goldbach.subprocess,'check_output',return_value='A\0'+self.state['gap']['file']+'\0'))
        self.desk = self.enterContext(patch.object(goldbach,'desk',return_value={'submitted':True}))
        self.comment = self.enterContext(patch.object(goldbach.subprocess,'run'))

    def test_submit_and_idempotent_retry(self):
        goldbach.submit(self.path,self.state,8,self.agent)
        self.assertEqual(self.desk.call_args.args[1]['agent'],self.agent)
        self.assertEqual(json.loads(self.path.read_text())['agent'],self.agent)
        goldbach.submit(self.path,self.state,8,self.agent)
        self.assertEqual(self.desk.call_count,1)
        self.assertEqual(self.comment.call_count,1)
        with self.assertRaises(SystemExit):
            goldbach.submit(self.path,self.state,8,dict(self.agent,model='other-model'))
        self.assertEqual(self.desk.call_count,1)

    def test_comment_retry_keeps_attribution_before_comment(self):
        self.comment.side_effect=RuntimeError('temporary comment failure')
        with self.assertRaises(RuntimeError):
            goldbach.submit(self.path,self.state,8,self.agent)
        saved=json.loads(self.path.read_text())
        self.assertEqual(saved['agent'],self.agent)
        self.assertEqual(saved['submitted_head'],'a'*40)
        self.comment.side_effect=None
        goldbach.submit(self.path,saved,8,self.agent)
        self.assertEqual(self.desk.call_count,2)
        self.assertEqual(self.desk.call_args_list[0].args[1],self.desk.call_args_list[1].args[1])

    def test_cli_accepts_new_harnesses(self):
        lease = self.path.parent / 'goldbach-lease.json'
        lease.write_text(json.dumps(self.state))
        for harness in ('kimi-code', 'qwen-code', 'codebuddy', 'github-copilot', 'cline', 'mistral-vibe'):
            with self.subTest(harness=harness), \
                 patch.object(sys, 'argv', ['goldbach.py', 'submit', '8', '--model', 'new-model-v1', '--harness', harness]), \
                 patch.object(goldbach, 'command', return_value=str(self.path.parent)), \
                 patch.object(goldbach, 'submit') as submit:
                goldbach.main()
                self.assertEqual(submit.call_args.args[3],
                                 {'model': 'new-model-v1', 'harness': harness, 'harness_version': 'unknown'})


if __name__ == '__main__':
    unittest.main()
