"""Submission provenance is self-reported, immutable and tied to an authorized head."""
import json
import re
import sqlite3
import sys
import tempfile
import unittest
from io import StringIO
from pathlib import Path
from unittest.mock import patch

from deploy.desk import (
    Desk, HARNESS_ICONS, HARNESS_NAMES, MODEL_ALIASES_FILE, MODEL_CATALOG,
    MODEL_EXACT_ALIASES, MODEL_NAME_ALIASES, MODEL_REGISTRY, agent_metadata,
    harness_brand_icon, model_brand_icon, model_catalog_payload,
    model_provider, model_ranking_name, provider_brand_icon,
)
from deploy import test_desk as desk_tests
from deploy.test_desk import GAPS, START
from tools import build_icons, goldbach, sync_models


class AttributionTests(unittest.TestCase):
    def test_model_provider_recognizes_author_and_family_aliases(self):
        for name, provider in {
            "gpt-6.2-sol": "OpenAI",
            "moonshotai/kimi-k3": "Moonshot AI",
            "qwen3.7-plus": "Alibaba",
            "step-3.5-flash": "StepFun",
            "glm5": "Z.ai",
            "nvidia/nemotron": "NVIDIA",
            "xiaomi/mimo": "Xiaomi",
            "inclusionai/ling": "InclusionAI",
            "aws/claude": "Anthropic",
            "aws/custom-model": "unknown",
            "openrouter/anthropic/claude-opus-4.5:free": "Anthropic",
            "bedrock/us.anthropic.claude-3-7-sonnet-20250219-v1:0": "Anthropic",
            "99bee5af-9ad7-44ea-afea-3d9db1bf1f2d/glm-5.4": "Z.ai",
            "hy4std": "Tencent",
            "hy4-flash-free": "Tencent",
            "big fat fish v4.1-flash": "DeepSeek",
            "nex-n2.6": "Nex AGI",
            "k3.1-pro": "Moonshot AI",
            "huggingface/deepseek-r1": "DeepSeek",
            "huggingface/smollm2-1.7b": "Hugging Face",
            "huggingface/zephyr-7b": "Hugging Face",
            "codex": "unknown",
            "custom-model": "unknown",
        }.items():
            with self.subTest(name=name):
                self.assertEqual(model_provider(name), provider)

    def test_brand_icon_single_source_of_truth(self):
        self.assertEqual(model_brand_icon("99bee5af-9ad7-44ea-afea-3d9db1bf1f2d/glm-5.4"), "zhipu")
        self.assertEqual(model_brand_icon("hy4std"), "hunyuan")
        self.assertEqual(model_brand_icon("hy4-flash-free"), "hunyuan")
        self.assertEqual(model_brand_icon("big fat fish v4.1-flash"), "deepseek")
        self.assertEqual(model_brand_icon("nex-n2.6"), "nex-agi")
        self.assertEqual(provider_brand_icon("Nex AGI"), "nex-agi")
        self.assertEqual(model_brand_icon("gemini-2.5-pro"), "gemini")
        self.assertEqual(provider_brand_icon("Google"), "google")
        self.assertEqual(model_brand_icon("kimi-k3"), "kimi")
        self.assertEqual(provider_brand_icon("Moonshot AI"), "moonshot")
        self.assertEqual(harness_brand_icon("minimax-code"), "minimax")
        self.assertEqual(harness_brand_icon("antigravity"), "antigravity")
        self.assertEqual(harness_brand_icon("zcode"), "zcode")
        self.assertEqual(harness_brand_icon("other"), "tool-other")
        self.assertIsNone(model_brand_icon("custom-model"))
        self.assertIsNone(model_brand_icon("aws/custom-model"))
        root = Path(__file__).resolve().parents[1]
        site_js = (root / "deploy/site.js").read_text()
        self.assertNotIn("agentBrandRules", site_js)
        self.assertNotIn("harnessBrandIcons", site_js)

    def test_svg_sprite_integrity_and_complete_symbol_coverage(self):
        import xml.etree.ElementTree as ET
        root = Path(__file__).resolve().parents[1]
        sprite_path = root / "deploy/agent-icons.svg"
        self.assertTrue(sprite_path.is_file())
        compiled, keys = build_icons.compile_sprite()
        self.assertEqual(sprite_path.read_text(encoding="utf-8"), compiled)
        # Strict XML parse check prevents duplicate attributes (e.g. duplicate xmlns) from breaking DOMParser.
        parsed = ET.fromstring(compiled)
        self.assertTrue(parsed.tag.endswith("}svg"))
        symbol_keys = set(keys)
        # Every icon key referenced by MODEL_REGISTRY, HARNESS_ICONS, and fallbacks must exist.
        referenced = {"provider-unknown", "tool-other"}
        for spec in MODEL_REGISTRY.values():
            if spec.get("icon"):
                referenced.add(spec["icon"])
            for _, fam_icon in spec.get("family_icons", ()):
                referenced.add(fam_icon)
        referenced.update(HARNESS_ICONS.values())
        self.assertEqual(referenced - symbol_keys, set())
        # All XML IDs inside the compiled sprite must be unique and every url(#...) must resolve.
        all_ids = re.findall(r'\bid="([^"]+)"', compiled)
        self.assertEqual(len(all_ids), len(set(all_ids)))
        id_set = set(all_ids)
        for ref in re.findall(r'url\(#([^)]+)\)', compiled):
            self.assertIn(ref, id_set)

    def test_model_catalog_payload_and_filtering(self):
        observed = [
            {"name": "glm-5.4", "provider": "Z.ai", "accepted": 3, "points": 12, "icon": "zhipu"},
            {"name": "gemini-neon", "provider": "Google", "accepted": 2, "points": 9, "icon": "gemini"},
            {"name": "tencent hunyuan hy", "provider": "Tencent", "accepted": 1, "points": 3, "icon": "hunyuan"},
            {"name": "mystery-x", "accepted": 1, "points": 2},
        ]
        payload = model_catalog_payload(observed, query="glm")
        self.assertEqual([item["id"] for item in payload["observed"]], ["glm-5.4"])
        self.assertTrue(any(item["id"] == "glm-5.4" and item["provider"] == "Z.ai" for item in payload["models"]))
        all_payload = model_catalog_payload(observed)
        observed_ids = {item["id"] for item in all_payload["observed"]}
        self.assertEqual(observed_ids, {"glm-5.4"})
        filtered = model_catalog_payload(observed, provider="Nex AGI")
        self.assertTrue(filtered["models"])
        self.assertTrue(all(item["provider"] == "Nex AGI" for item in filtered["models"]))
        self.assertEqual(filtered["harnesses"], list(HARNESS_NAMES))
        # Org aliases also resolve to their canonical provider when filtering.
        alias_filtered = model_catalog_payload(observed, provider="zhipu")
        self.assertTrue(alias_filtered["models"])
        self.assertTrue(all(item["provider"] == "Z.ai" for item in alias_filtered["models"]))
        self.assertEqual([item["id"] for item in alias_filtered["observed"]], ["glm-5.4"])
        # Default pagination caps payload size and omits static metadata on subsequent pages.
        page1 = model_catalog_payload(observed, offset=0, limit=10)
        self.assertEqual(len(page1["models"]), 10)
        self.assertTrue(page1["has_more"])
        self.assertIn("providers", page1)
        page2 = model_catalog_payload(observed, offset=10, limit=10)
        self.assertEqual(len(page2["models"]), 10)
        self.assertNotIn("providers", page2)
        self.assertNotIn("harnesses", page2)

    def test_standalone_alias_file_does_not_pollute_catalog(self):
        self.assertTrue(MODEL_ALIASES_FILE.is_file())
        data = json.loads(MODEL_ALIASES_FILE.read_text(encoding="utf-8"))
        self.assertEqual(set(data["model_aliases"]), set(MODEL_NAME_ALIASES))
        self.assertEqual(set(data["provider_aliases"]), set(MODEL_EXACT_ALIASES))
        # No alias key may appear in MODEL_CATALOG.
        self.assertEqual(set(MODEL_NAME_ALIASES) & set(MODEL_CATALOG), set())
        self.assertEqual(set(MODEL_EXACT_ALIASES) & set(MODEL_CATALOG), set())
        # Every alias target must be clean, non-chained, and recognized.
        for alias, target in MODEL_NAME_ALIASES.items():
            with self.subTest(alias=alias, target=target):
                self.assertNotIn(" ", target)
                self.assertNotIn(target, MODEL_NAME_ALIASES)
                self.assertNotEqual(model_provider(target), "unknown")
                self.assertEqual(model_ranking_name(alias), target)
        # Verify live multi-desk alias merges.
        for alias, canonical in {
            "big fat fish v4.1-flash": "deepseek-v4.1-flash",
            "gpt-6 astra pro": "gpt-6-astra-pro",
            "minimax m78": "minimax-m78",
            "gemini-neon": "gemini-4-neon",
            "gemini 4": "gemini-4",
            "gemini-4-carbon-high": "gemini-4-carbon",
            "gemini 4 hydrogen": "gemini-4-hydrogen",
            "gemini-4-hydrogen-high": "gemini-4-hydrogen",
            "k3.1-pro": "kimi-k3.1-pro",
        }.items():
            self.assertEqual(model_ranking_name(alias), canonical)
        self.assertEqual(model_brand_icon("k3.1-pro"), "kimi")

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
                      {'model': '<script>'}, {'model': 'a\nb'}, {'harness': 'made-up'}, {'extra': 1},
                      {'model': '99bee5af-9ad7-44ea-afea-3d9db1bf1f2d/glm-5.4', 'harness': 'codex'}):
            with self.subTest(value=value), self.assertRaises(ValueError):
                agent_metadata(value)
        token = self.helper.claim()
        self.assertEqual(self.submit(token, {'harness': 'made-up'})[0], 400)
        self.assertEqual(self.submit(token, self.agent)[0], 200)

    def test_historical_harness_alias_requires_matching_pr_and_head(self):
        head = "a" * 40
        rows = [(101, head, "other"), (101, "b" * 40, "other"), (102, head, "other")]
        with self.desk.transaction(write=True) as conn:
            for run, (pr, revision, harness) in enumerate(rows, 1):
                conn.execute("""
                    INSERT INTO goldbach_leases
                      (token_hash, gap, statement_sha256, handle, ip_key, claimed_at, expires_at,
                       absolute_expires_at, pr, head, run_id, finished_at, verdict, model, harness, points)
                    VALUES (?, ?, 'hash', 'alice', 'network', 0, 0, 0, ?, ?, ?, ?, 'ACCEPTED', 'model-a', ?, 5)
                """, (str(run), GAPS[run - 1]["id"], pr, revision, run, START + run, harness))
            with patch("deploy.desk.HISTORICAL_HARNESSES", {(101, head): "minimax-code"}):
                ranking = self.desk.agent_rankings(conn, START + 10)
            self.assertEqual(ranking["harnesses"], [
                {"name": "other", "accepted": 2, "points": 10, "icon": "tool-other"},
                {"name": "minimax-code", "accepted": 1, "points": 5, "icon": "minimax"},
            ])
            self.assertEqual(ranking["models"], [{"name": "model-a", "accepted": 3, "points": 15}])
            self.assertEqual(conn.execute("SELECT DISTINCT harness FROM goldbach_leases").fetchone()[0], "other")

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
        self.assertEqual(
            model_ranking_name('99bee5af-9ad7-44ea-afea-3d9db1bf1f2d/glm-5.4'),
            'glm-5.4',
        )
        self.assertEqual(
            model_ranking_name('big fat fish v4.1-flash'),
            'deepseek-v4.1-flash',
        )
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
            {'name': 'gpt-6.2-astra', 'accepted': 26, 'points': 26, 'provider': 'OpenAI', 'icon': 'openai'},
            {'name': 'gpt-6.1-astra', 'accepted': 1, 'points': 1, 'provider': 'OpenAI', 'icon': 'openai'},
            {'name': 'gpt-6.2-sol', 'accepted': 1, 'points': 1, 'provider': 'OpenAI', 'icon': 'openai'},
        ])
        self.assertEqual(ranks['harnesses'], [
            {'name': 'codex', 'accepted': 17, 'points': 17, 'icon': 'codex'},
            {'name': 'kimi-code', 'accepted': 9, 'points': 9, 'icon': 'kimi'},
            {'name': 'other', 'accepted': 1, 'points': 1, 'icon': 'tool-other'},
            {'name': 'qwen-code', 'accepted': 1, 'points': 1, 'icon': 'qwen'},
        ])
        self.assertEqual(ranks['proofs'], 28)
        records = [{'run_id': 18, 'lemma_id': 'lemma-18'}]
        with self.desk.transaction() as conn:
            self.desk.annotate_verdicts(records, conn)
        self.assertEqual(records[0]['agent']['model'], 'gpt-6.2 astra high')

    def test_explicit_model_name_alias_merges_rankings_and_preserves_record(self):
        with self.desk.transaction(write=True) as conn:
            for run, gap, model, pts in (
                (1, 'lemma-1', 'deepseek-v4.1-flash', 87),
                (2, 'lemma-2', 'big fat fish v4.1-flash', 27),
            ):
                conn.execute("""INSERT INTO goldbach_leases
                    (token_hash,gap,statement_sha256,handle,ip_key,claimed_at,expires_at,
                     absolute_expires_at,pr,head,run_id,finished_at,verdict,model,harness,agent_reported,points)
                    VALUES (?,?,'hash','alice','network',0,0,0,?,'head',?,?,'ACCEPTED',?,'opencode',1,?)
                """, (str(run), gap, run, run, START + run, model, pts))
        ranks = self.helper.status(now=START + 10)['agent_rankings']
        self.assertEqual(ranks['models'], [
            {'name': 'deepseek-v4.1-flash', 'accepted': 2, 'points': 114, 'provider': 'DeepSeek', 'icon': 'deepseek'},
        ])
        self.assertEqual(ranks['providers'], [
            {'name': 'DeepSeek', 'accepted': 2, 'points': 114, 'icon': 'deepseek', 'models': ranks['models']},
        ])
        records = [{'run_id': 2, 'lemma_id': 'lemma-2'}]
        with self.desk.transaction() as conn:
            self.desk.annotate_verdicts(records, conn)
        self.assertEqual(records[0]['agent']['model'], 'big fat fish v4.1-flash')

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
        self.assertEqual({k: v for k, v in ranks.items() if k != 'providers'}, {'models': [{'name': 'model-b', 'accepted': 1, 'points': 1}], 'harnesses': [{'name': 'codex', 'accepted': 1, 'points': 1, 'icon': 'codex'}], 'proofs': 1})

    def test_first_acceptance_unknown_history_and_separate_models(self):
        with self.desk.transaction(write=True) as conn:
            for run, gap, model, harness, verdict in [
                (1, 'first', 'gpt-6', 'codex', 'ACCEPTED'),
                (2, 'first', 'model-b', 'cursor', 'ACCEPTED'),
                (3, 'second', 'gpt-6.2-sol', 'codex', 'ACCEPTED'),
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
        self.assertEqual(ranks['models'], [
            {'name': 'gpt-6', 'accepted': 1, 'points': 1, 'provider': 'OpenAI', 'icon': 'openai'},
            {'name': 'gpt-6.2-sol', 'accepted': 1, 'points': 1, 'provider': 'OpenAI', 'icon': 'openai'},
            {'name': 'model-c', 'accepted': 1, 'points': 1},
        ])
        self.assertEqual(ranks['providers'], [
            {'name': 'OpenAI', 'accepted': 2, 'points': 2, 'icon': 'openai', 'models': ranks['models'][:2]},
            {'name': 'unknown', 'accepted': 1, 'points': 1, 'models': ranks['models'][2:]},
        ])
        self.assertEqual(ranks['harnesses'], [
            {'name': 'codex', 'accepted': 2, 'points': 2, 'icon': 'codex'},
            {'name': 'cursor', 'accepted': 1, 'points': 1, 'icon': 'cursor'},
        ])
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

    def test_cli_source_governance_rejects_noisy_model_ids(self):
        lease = self.path.parent / 'goldbach-lease.json'
        lease.write_text(json.dumps(self.state))
        for bad in (
            '99bee5af-9ad7-44ea-afea-3d9db1bf1f2d/glm-5.4',
            'openrouter/anthropic/claude-opus-4.5',
            'aws/claude-3.7-sonnet',
            'glm-5.4:free',
            'codex',
        ):
            with self.subTest(model=bad), \
                 patch.object(sys, 'argv', ['goldbach.py', 'submit', '8', '--model', bad, '--harness', 'codex']), \
                 patch.object(goldbach, 'command', return_value=str(self.path.parent)), \
                 patch('sys.stderr', new=StringIO()), \
                 self.assertRaises(SystemExit):
                goldbach.main()
        # Escape hatch allows explicit override if intentional.
        with patch.object(sys, 'argv', ['goldbach.py', 'submit', '8', '--model', 'glm-5.4:free', '--harness', 'codex', '--force-model']), \
             patch.object(goldbach, 'command', return_value=str(self.path.parent)), \
             patch.object(goldbach, 'submit') as submit:
            goldbach.main()
            self.assertEqual(submit.call_args.args[3]['model'], 'glm-5.4:free')

    def test_cli_models_command_offline_json(self):
        buf = StringIO()
        with patch.object(sys, 'argv', ['goldbach.py', 'models', '--offline', '--search', 'glm', '--json']), \
             patch('sys.stdout', new=buf):
            goldbach.main()
        payload = json.loads(buf.getvalue())
        self.assertTrue(any(m['id'] == 'glm-5.4' and m['provider'] == 'Z.ai' for m in payload['models']))

    def test_sync_models_extract_and_audit(self):
        openrouter_sample = {
            "data": [
                {"id": "z-ai/glm-5.4:free"},
                {"id": "nex-agi/nex-n2.6"},
                {"id": "unknown-vendor/mystery-1"},
            ]
        }
        extracted = sync_models.extract_upstream_models(openrouter_sample)
        self.assertEqual(extracted["glm-5.4"], "Z.ai")
        self.assertEqual(extracted["nex-n2.6"], "Nex AGI")
        self.assertNotIn("mystery-1", extracted)

        models_dev_sample = {
            "anthropic": {"models": {"claude-opus-4.6": {}}},
            "tencent": {"models": {"hunyuan-t1": {}}},
        }
        extracted_dev = sync_models.extract_upstream_models(models_dev_sample)
        self.assertEqual(extracted_dev["claude-opus-4.6"], "Anthropic")
        self.assertEqual(extracted_dev["hunyuan-t1"], "Tencent")

        audit = sync_models.audit_models([
            {"name": "99bee5af-9ad7-44ea-afea-3d9db1bf1f2d/glm-5.4", "accepted": 1, "points": 6},
            {"name": "hy4std", "accepted": 1, "points": 58},
            {"name": "big fat fish v4.1-flash", "accepted": 2, "points": 27},
            {"name": "nex-n2.6", "accepted": 1, "points": 5},
            {"name": "truly-unknown-7b", "accepted": 2, "points": 11},
        ])
        self.assertEqual([row["name"] for row in audit], ["truly-unknown-7b"])


if __name__ == '__main__':
    unittest.main()
