'use strict';

const lang = document.documentElement.lang.startsWith('zh') ? 'zh' : 'en';
const topic = document.body.dataset.problem;
const guideUrl = 'https://www.movan.tech/goldbach/' + (topic ? 'problems/' + topic + '/' : '') +
  (lang === 'zh' ? 'join-zh.txt' : 'join.txt');
const claimCommand = 'python tools/goldbach.py claim' + (topic ? ' --problem ' + topic : '');
const repository = 'https://github.com/CGandGameEngineLearner/goldbach-proofs';
const menu = document.querySelector('.menu-toggle');
const navigation = document.getElementById('site-nav');
menu.addEventListener('click', () => {
  menu.setAttribute('aria-expanded', String(navigation.classList.toggle('expanded')));
});
navigation.addEventListener('click', () => {
  navigation.classList.remove('expanded');
  menu.setAttribute('aria-expanded', 'false');
});
const strings = {
  zh: {
    open: '待证', proved: '已通过', accepted: '已通过', rejected: '已拒绝',
    assignments: { working: '已领取', submitted: '已提交', checking: '验证中' },
    run: '查看运行', latestRun: '最近运行', noRun: '暂无', attempt: '运行尝试',
    manifest: '查看证据清单', empty: '没有匹配的引理。', noRecords: '还没有权威验证记录。',
    count: n => '找到 ' + n + ' 条引理。',
    failure: '暂时无法获取实时数据。', published: '查看 GitHub 命题清单',
    copied: '已复制', copyManual: '请复制已选中的提示词。',
    stale: '暂时无法刷新，正在显示上次获取的数据。',
    deskUnavailable: '暂时无法获取社区数据。',
    noActivity: '暂无参与记录。',
    noContributors: '暂无有署名的通过记录。',
    noHourContributors: '最近一小时暂无首次通过的引理。',
    rankingsUnavailable: '暂时无法获取贡献榜。',
    rankingsCount: n => '共 ' + n + ' 位贡献者。',
    rankingsSummary: (people, proofs) => people + ' 位贡献者共通过 ' + proofs + ' 条引理，按首次核验积分排列。',
    rankingPeriods: { hour: '最近一小时', all_time: '累计' },
    justNow: '刚刚',
    participant: '参与者',
    activities: {
      claimed: '领取引理', submitted: '登记提交', checking: '开始验证',
      released: '归还引理', accepted: '验证通过', rejected: '验证拒绝', expired: '任务凭证过期'
    },
    event: '任务状态更新',
    verifiedCount: n => n.toLocaleString(locale) + ' 题',
    pointsUnit: '分',
    pullRequest: '查看 PR',
    allPrograms: '全部路线',
    programCount: (verified, published) => verified + ' / ' + published + ' 已通过',
    pageRange: (first, last, total) => '第 ' + first + '–' + last + ' 条，共 ' + total + ' 条',
    file: '证明文件',
    copyLemma: '复制这条引理的参与提示词',
    occupied: '这条引理当前正在处理。',
    alreadyVerified: '这条引理已通过权威验证。',
    lemmaPrompt: gap => '读取 ' + guideUrl + '，按指南用 ' + claimCommand + ' ' + gap.id + ' 领取并验证这一条引理。可跨猜想导入全站已验证社区模块，完整清单见领取指南。'
      + '同一题的积分归研究台最先记录权威 Lean ACCEPTED 的提交者。'
      + (gap.takes_cuts ? '也可用 ' + claimCommand + ' ' + gap.id + ' --kind cut 提交拆题，每套经 Lean 核验并被采用的拆法另加 1 分。' : '')
      + (gap.imports?.length ? '本题推荐  ' + gap.imports.join('、') + '。' : '')
      + '可查阅网上资料，把相关方法形式化到指定的 Lean 文件，并在 PR 中注明来源。如果无法领取这条引理，请说明原因，不要改领其他题。'
  },
  en: {
    open: 'Open', proved: 'Verified', accepted: 'Accepted', rejected: 'Rejected',
    assignments: { working: 'Claimed', submitted: 'Submitted', checking: 'Checking' },
    run: 'View run', latestRun: 'Latest run', noRun: 'Pending', attempt: 'Attempt',
    manifest: 'View evidence manifest', empty: 'No matching lemmas.', noRecords: 'No authoritative runs have been recorded.',
    count: n => n === 1 ? '1 matching lemma.' : n + ' matching lemmas.',
    failure: 'Live data is temporarily unavailable.', published: 'View statements on GitHub',
    copied: 'Copied', copyManual: 'Copy the selected prompt.',
    stale: 'Refresh failed. Showing the last available data.',
    deskUnavailable: 'Community data is temporarily unavailable.',
    noActivity: 'No community activity yet.',
    noContributors: 'No attributed proofs have passed verification yet.',
    noHourContributors: 'No lemmas passed for the first time in the past hour.',
    rankingsUnavailable: 'The leaderboard is temporarily unavailable.',
    rankingsCount: n => n + (n === 1 ? ' contributor.' : ' contributors.'),
    rankingsSummary: (people, proofs) => people + (people === '1' ? ' contributor has ' : ' contributors have ') +
      proofs + (proofs === '1' ? ' accepted proof, ranked by points.' : ' accepted proofs, ranked by points.'),
    rankingPeriods: { hour: 'This hour', all_time: 'All time' },
    justNow: 'Just now',
    participant: 'Participant',
    activities: {
      claimed: 'Claimed a lemma', submitted: 'Registered a submission', checking: 'Started verification',
      released: 'Returned a lemma', accepted: 'Proof accepted', rejected: 'Proof rejected', expired: 'Lease expired'
    },
    event: 'Task status changed',
    verifiedCount: n => n.toLocaleString(locale) + (n === 1 ? ' proof' : ' proofs'),
    pointsUnit: 'pts',
    pullRequest: 'View PR',
    allPrograms: 'All programs',
    programCount: (verified, published) => verified + ' / ' + published + ' verified',
    pageRange: (first, last, total) => first + '–' + last + ' of ' + total + ' lemmas',
    file: 'Proof file',
    copyLemma: 'Copy this lemma’s join prompt',
    occupied: 'This lemma is currently in progress.',
    alreadyVerified: 'The authoritative verifier has accepted this lemma.',
    lemmaPrompt: gap => 'Read ' + guideUrl + ' and follow it to claim and verify exactly ' + gap.id + ' with ' + claimCommand + ' ' + gap.id + '. Verified community modules are available across conjectures (see the guide). '
      + "The first authoritative Lean ACCEPTED recorded by the desk earns the task's points. "
      + (gap.takes_cuts ? 'You can also use ' + claimCommand + ' ' + gap.id + ' --kind cut. Each Lean-verified cut adopted by the desk earns a separate point. ' : '')
      + (gap.imports?.length ? 'Suggested imports include ' + gap.imports.join(', ') + '. ' : '')
      + 'You may research methods online. Formalize the relevant steps in your assigned Lean file and cite your sources in the PR. If that lemma is unavailable, report why and do not choose another.'
  }
}[lang];

function element(tag, text, className) {
  const node = document.createElement(tag);
  if (text !== undefined) node.textContent = text;
  if (className) node.className = className;
  return node;
}

function anchor(label, href, className) {
  const link = element('a', label, className);
  link.href = href;
  return link;
}

function runLink(run, label) {
  let path = '/actions/runs/' + run.run_id;
  if (Number.isSafeInteger(run.check_id) && run.check_id > 0) {
    path = '/runs/' + run.check_id;
  } else if (typeof run.head_sha === 'string' && /^[a-f0-9]{40}$/.test(run.head_sha)) {
    path = '/commit/' + run.head_sha;
  }
  return anchor(label + ' ↗', repository + path, 'evidence-link');
}

async function fetchPublicJson(url) {
  const response = await fetch(url, { signal: AbortSignal.timeout(15000) });
  if (!response.ok) throw new Error("Public data unavailable");
  return response.json();
}

function loadDisclosure(target, request, render) {
  target.setAttribute('aria-busy', 'true');
  const loadingLabel = lang === 'zh' ? '正在加载详情…' : 'Loading details…';
  target.replaceChildren(element('p', loadingLabel, 'detail-context'));
  request().then(data => {
    if (!target.isConnected) return;
    target.removeAttribute('aria-busy');
    render(data);
  }).catch(() => {
    if (!target.isConnected) return;
    target.removeAttribute('aria-busy');
    const retry = element('button', lang === 'zh' ? '重试' : 'Retry', 'button');
    retry.type = 'button';
    retry.addEventListener('click', () => loadDisclosure(target, request, render));
    target.replaceChildren(element('p', strings.failure, 'detail-context'), retry);
  });
}

const taskDetails = new Map();

function loadTaskDetail(id) {
  const now = Date.now();
  const cached = taskDetails.get(id);
  if (cached && cached.until > now) return cached.request;
  const entry = { until: now + 30000 };
  entry.request = fetchPublicJson('api/task?lemma=' + encodeURIComponent(id)).catch(error => {
    if (taskDetails.get(id) === entry) taskDetails.delete(id);
    throw error;
  });
  taskDetails.delete(id);
  taskDetails.set(id, entry);
  if (taskDetails.size > 48) taskDetails.delete(taskDetails.keys().next().value);
  return entry.request;
}

function detailSearch(scope, refresh) {
  let active = '';
  let matches = new Set();
  let debounce;
  let pending;

  return {
    update(query) {
      if (active === query) return;
      active = query;
      matches = new Set();
      window.clearTimeout(debounce);
      pending?.abort();
      if (query.length === 0 || query.length > 500) return;
      debounce = window.setTimeout(async () => {
        const controller = new AbortController();
        pending = controller;
        const params = new URLSearchParams({q: query, lang, scope});
        try {
          const response = await fetch('api/task-search?' + params, {
            signal: AbortSignal.any([controller.signal, AbortSignal.timeout(10000)]),
          });
          if (!response.ok) return;
          const data = await response.json();
          if (!controller.signal.aborted && active === query) {
            matches = new Set(data.ids);
            refresh();
          }
        } catch {
          // Titles and IDs can still be searched locally.
        }
      }, 250);
    },
    matches(query, id) {
      return query === active && matches.has(id);
    },
  };
}

function cutEvidence(gap) {
  const zh = lang === 'zh';
  const block = element('div', undefined, 'detail-context');
  const reasons = {
    cuts_disabled: zh ? '此题未开启拆题' : 'Cuts are disabled for this task',
    cut_depth_limit: zh ? '已到拆题深度上限' : 'Cut depth limit reached',
    cut_limit: zh ? '有效拆法数已达上限' : 'Live cut limit reached',
    claims_closed: closedClaimLabel(),
    settled: zh ? '此题已结案' : 'This task is settled'
  };
  const states = {
    live: zh ? '可继续' : 'Live', refuted: zh ? '前提已证伪' : 'Premise refuted',
    completed: zh ? '已组合证明' : 'Completed', superseded: zh ? '父题已结案' : 'Parent settled',
    surplus: zh ? '未采用' : 'Unused'
  };
  block.append(element('p', [
    gap.takes_cuts ? (zh ? '可提交拆题' : 'Open for cuts') : reasons[gap.cut_reason],
    (zh ? '深度 ' : 'Depth ') + (gap.depth || 0),
    (zh ? '有效拆法 ' : 'Live cuts ') + (gap.reductions_live || 0)
  ].filter(Boolean).join(' · ')));
  const credit = (row, item) => {
    if (item.handle) row.append(' · @' + item.handle);
    if (item.pr) row.append(' · ', anchor('PR #' + item.pr, repository + '/pull/' + item.pr));
    if (item.head) row.append(' · ', runLink({run_id: item.run_id || item.run, head_sha: item.head}, item.head.slice(0, 8)));
  };
  for (const cut of gap.cuts || []) {
    const row = element('p', (zh ? '拆法' : 'Cut') + ' · ' + states[cut.status]);
    if (cut.reason) row.append(' · ' + (reasons[cut.reason] || cut.reason));
    if (cut.points) row.append(' · +' + cut.points.toLocaleString(locale) + ' ' + strings.pointsUnit);
    credit(row, cut);
    for (const id of cut.children) row.append(' · ', anchor(id, '?lang=' + lang + '&lemma=' + encodeURIComponent(id)));
    block.append(row);
  }
  if (gap.cut_origin?.contributor_wording) {
    block.append(anchor(zh ? '查看拆题作者的双语说明' : 'Bilingual wording from the cut author',
      repository + '/pull/' + gap.cut_origin.pr));
  }
  if (gap.refutation?.handle) {
    const row = element('p', zh ? '已核验反证' : 'Verified refutation');
    credit(row, gap.refutation);
    if (gap.refutation.module) {
      row.append(' · ', anchor(zh ? '反证源码' : 'Refutation source', repository + '/blob/' +
        gap.refutation.head + '/lean/' + gap.refutation.module.replaceAll('.', '/') + '.lean'));
    }
    block.append(row);
  }
  if (gap.assembly) {
    const details = element('details');
    details.append(element('summary', zh ? '父题组合证明与贡献者' : 'Composed proof and contributors'));
    const add = (node) => {
      const row = element('p', node.gap);
      credit(row, node);
      details.append(row);
      for (const premise of node.premises || []) add(premise);
    };
    add(gap.assembly.proof);
    details.append(element('pre', gap.assembly.source));
    block.append(details);
  }
  return block;
}

function verdictTag(label, status) {
  return element('span', label, status ? 'verdict verdict-' + status : 'verdict');
}

const lemmaRows = document.getElementById('lemma-rows');
const lemmaSearch = document.getElementById('lemma-search');
const lemmaState = document.getElementById('lemma-state');
const verificationLog = document.getElementById('verification-log');
const deskNotice = document.getElementById('desk-notice');
const deskActivity = document.getElementById('desk-activity');
const rankingsList = document.getElementById('rankings-list');
const rankingsModes = Array.from(document.querySelectorAll('[data-ranking-mode]'));
const rankingsAnnouncement = document.getElementById('rankings-announcement');
const RANKINGS_BATCH = 12;
let rankingsData = null;
let rankingsSnapshot = null;
let rankingMode = null;
let agentRankingsData = null;
let rankingsEpoch = 0;
let rankingObserver = null;
let activeRankingScroll = null;
const rankingFeeds = {};
const locale = document.documentElement.lang;
const eventTime = new Intl.DateTimeFormat(locale, { dateStyle: 'medium', timeStyle: 'short' });
const relativeTime = new Intl.RelativeTimeFormat(locale, { numeric: 'auto' });

const mapContext = document.getElementById('map-context');
const mapReset = document.getElementById('map-reset');
const programButtons = Array.from(document.querySelectorAll('[data-program]'));
const programs = new Map(programButtons.map(button => [button.dataset.program, button]));
const lemmaDialog = document.getElementById('lemma-detail');
const detailContent = document.getElementById('lemma-detail-content');
const pageRange = document.getElementById('lemma-page-range');
const previousPage = document.getElementById('lemma-prev');
const nextPage = document.getElementById('lemma-next');
const pageSelect = document.getElementById('lemma-page');
const pageSize = 24;

let publishedGaps = [];
let gapRoutes = new Map();
let assignments = {};
let selectedProgram = '';
let selectedGap = null;
let lemmaPage = 1;
let loading = false;
let lastGaps = null;
let lastResults = null;
let lastDesk = null;

function messageRow(label, link) {
  const row = element('tr');
  const cell = element('td', label, 'empty-state');
  cell.colSpan = 3;
  if (link) cell.append(link);
  row.append(cell);
  return row;
}

function programOf(gap) {
  if (programs.has(gap.route_id)) return gap.route_id;
  if (programs.has(gap.track)) return gap.track;
  if (programs.has(gap.program)) return gap.program;
  return gap.route_id || gap.track || 'unclassified';
}

function programName(key) {
  return programs.get(key)?.querySelector('.program-name').textContent ?? '';
}

function assigned(gap) {
  return !gap.proved && Object.hasOwn(strings.assignments, assignments[gap.id]);
}

function closedClaimLabel() {
  return lang === 'zh' ? '已停止新领取' : 'Closed to new claims';
}

function gapStatus(gap) {
  if (gap.refutation) {
    const verified = gap.refutation.status === 'verified';
    const label = lang === 'zh' ? (verified ? '已证伪' : '反证待核验') : (verified ? 'Refuted' : 'Refutation under review');
    return { label, kind: 'occupied', style: 'in-progress' };
  }
  if (gap.resolved && !gap.proved) return { label: lang === 'zh' ? '已解决' : 'Resolved', kind: 'verified', style: 'accepted' };
  if (gap.proved) return { label: strings.proved, kind: 'verified', style: 'accepted' };
  if (gap.claims_closed) return { label: closedClaimLabel(), kind: 'closed', style: '' };
  if (assigned(gap)) {
    return { label: strings.assignments[assignments[gap.id]], kind: 'occupied', style: 'in-progress' };
  }
  return { label: strings.open, kind: 'available', style: '' };
}

function canClaim(gap) {
  return !gap.claims_closed && !gap.refutation && !gap.proved && !gap.resolved && (!assigned(gap) || gap.parallel === true);
}

function renderProgramCounts() {
  const counts = new Map(Array.from(programs.keys(), key => [key, { published: 0, verified: 0, active: 0 }]));
  for (const gap of publishedGaps) {
    const count = counts.get(programOf(gap));
    if (!count) continue;
    count.published += 1;
    if (gap.proved) count.verified += 1;
    if (assigned(gap)) count.active++;
  }
  for (const [key, count] of counts) {
    const button = programs.get(key);
    button.classList.toggle('route-active', count.active > 0);
    button.querySelector('.program-count').textContent = strings.programCount(count.verified, count.published)
      + ' · ' + count.active + (lang === 'zh' ? ' 进行中' : ' in progress');
  }
}

function chooseProgram(program) {
  selectedProgram = program;
  for (const [key, button] of programs) {
    button.setAttribute('aria-pressed', String(key === program));
  }
  mapContext.textContent = programName(program) || strings.allPrograms;
  mapReset.hidden = !program;
  lemmaPage = 1;
  if (lastGaps !== null) renderLemmas();
  researchMap.setProgram(program);
}

for (const [key, button] of programs) {
  button.addEventListener('click', () => chooseProgram(selectedProgram === key ? '' : key));
}
mapReset.addEventListener('click', () => {
  programs.get(selectedProgram)?.focus();
  chooseProgram('');
});

function updateRouteActivity(gaps) {
  const byId = new Map(gaps.map(gap => [gap.id, gap]));
  for (const panel of document.querySelectorAll('.route-panel')) {
    const counts = { working: 0, submitted: 0, checking: 0, proved: 0 };
    for (const link of panel.querySelectorAll('[data-roadmap-task]')) {
      const gap = byId.get(link.dataset.roadmapTask);
      if (!gap) continue;
      const state = gap.proved ? 'proved' : assignments[gap.id];
      if (Object.hasOwn(counts, state)) counts[state]++;
      const badge = link.querySelector('.task-activity');
      if (Object.hasOwn(strings.assignments, state)) {
        const current = badge || element('small', '', 'task-activity');
        current.textContent = strings.assignments[state];
        if (!badge) link.append(current);
      } else if (badge) badge.remove();
    }
    const active = counts.working + counts.submitted + counts.checking;
    panel.classList.toggle('route-active', active > 0);
    const parts = ['working', 'submitted', 'checking']
      .filter(key => counts[key]).map(key => counts[key] + ' ' + strings.assignments[key]);
    if (!active) parts.push(lang === 'zh' ? '暂无进行中任务' : 'No active tasks');
    parts.push(counts.proved + (lang === 'zh' ? ' 已核验' : ' verified'));
    panel.querySelector('[data-route-status]').textContent = ' · ' + parts.join(' · ');
  }
}

function openGap(id) {
  selectedGap = id;
  renderGapDetail();
  if (!lemmaDialog.open) lemmaDialog.showModal();
  detailContent.scrollTop = 0;
}

document.getElementById('roadmap')?.addEventListener('click', event => {
    const link = event.target.closest('a[data-roadmap-task]');
    if (!link || event.ctrlKey || event.metaKey || event.shiftKey || event.altKey) return;
    if (publishedGaps.some(gap => gap.id === link.dataset.roadmapTask)) {
      event.preventDefault();
      openGap(link.dataset.roadmapTask);
    }
});

function renderGapDetail() {
  const gap = publishedGaps.find(entry => entry.id === selectedGap);
  if (!gap) return;
  const placeholder = element('div');
  detailContent.replaceChildren(placeholder);
  loadDisclosure(placeholder, () => loadTaskDetail(gap.id), detail => drawGapDetail({ ...gap, ...detail }));
}

function drawGapDetail(gap) {
  const status = gapStatus(gap);
  const identity = element('div', undefined, 'detail-identity');
  identity.append(element('code', gap.id), verdictTag(status.label, status.style));
  const role = {
    endpoint: lang === 'zh' ? '与强哥德巴赫猜想等价的总目标' : 'Final target equivalent to strong Goldbach',
    target: lang === 'zh' ? '待突破的解析估计' : 'Open analytic target',
    conditional: lang === 'zh' ? '需使用命题中所列假设' : 'Conditional on the stated hypotheses'
  }[gap.role];
  const challenge = gap.challenge_only && !gap.claims_closed && (lang === 'zh' ? '核心开放难题 · 仅按 ID 主动挑战' : 'Open research challenge · claim explicitly by ID');
  const context = [programName(programOf(gap)), role, challenge].filter(Boolean).join(' · ');
  detailContent.replaceChildren(
    identity,
    element('h3', gap.plain_statement[lang]),
    element('p', context, 'detail-context'),
    element('pre', gap.statement, 'detail-statement')
  );

  detailContent.append(cutEvidence(gap));
  if (gap.brief?.[lang]) detailContent.append(element('p', gap.brief[lang], 'detail-context'));
  if (gap.source) detailContent.append(anchor(lang === 'zh' ? '阅读来源 ↗' : 'Read the source ↗', gap.source, 'evidence-link'));
  if (canClaim(gap) && gap.parallel) detailContent.append(element('p',
    lang === 'zh' ? '此问题开放给多个参与者独立试证。' : 'This problem accepts independent proof attempts in parallel.', 'detail-context'));
  if (gap.file) {
    const file = element('p', undefined, 'detail-file');
    file.append(element('strong', strings.file), element('code', gap.file));
    detailContent.append(file);
  }
  if (gap.latest) {
    detailContent.append(runLink(gap.latest, strings.latestRun));
  }
  if (gap.refutation) {
    if (!gap.refutation.handle) detailContent.append(anchor(status.label + ' · PR #' + gap.refutation.pr, repository + '/pull/' + gap.refutation.pr, 'evidence-link'));
    return;
  }
  if (!canClaim(gap)) {
    const reason = gap.proved ? strings.alreadyVerified : gap.claims_closed ? closedClaimLabel() : strings.occupied;
    detailContent.append(element('p', reason, 'detail-context'));
    return;
  }
  const join = element('div', undefined, 'detail-join');
  const copy = element('button', strings.copyLemma, 'button button-primary');
  copy.type = 'button';
  const prompt = element('p', strings.lemmaPrompt(gap), 'join-prompt');
  const announcement = element('span', undefined, 'join-feedback');
  announcement.setAttribute('role', 'status');
  bindPromptCopy(copy, prompt, announcement);
  join.append(copy, prompt, announcement);
  detailContent.append(join);
}

lemmaDialog.addEventListener('close', () => { selectedGap = null; });

function lemmaRow(gap) {
  const row = element('tr');
  const claim = element('td');
  const button = element('button', gap.plain_statement[lang], 'statement-link');
  button.type = 'button';
  button.addEventListener('click', () => openGap(gap.id));
  claim.append(element('code', gap.id, 'statement-id'), button);
  const context = programName(programOf(gap));
  if (Number.isSafeInteger(gap.points)) {
    const points = gap.points.toLocaleString(locale);
    claim.append(element('span', lang === 'zh' ? points + ' 分' : points + ' pts', 'row-context'));
  }
  if (context) claim.append(element('span', context, 'row-context'));

  const statusCell = element('td');
  const status = gapStatus(gap);
  statusCell.append(verdictTag(status.label, status.style));
  const evidence = element('td');
  if (gap.latest) {
    evidence.append(runLink(gap.latest, strings.latestRun));
  } else {
    evidence.append(element('span', strings.noRun));
  }
  row.append(claim, statusCell, evidence);
  return row;
}

const lemmaDetailSearch = detailSearch('all', renderLemmas);

function renderLemmas() {
  const query = lemmaSearch.value.trim().toLowerCase();
  lemmaDetailSearch.update(query);
  const selection = lemmaState.value;
  const visibleGaps = publishedGaps.filter(gap => {
    if (selectedProgram && programOf(gap) !== selectedProgram) return false;
    if (selection === 'proved' && !gap.proved) return false;
    if (selection === 'open' && gap.proved) return false;
    if (selection === 'progress' && !assigned(gap)) return false;
    if (selection === 'available' && !canClaim(gap)) return false;
    if (!query) return true;
    const program = programOf(gap);
    const content = [
      gap.id, gap.plain_statement.zh, gap.plain_statement.en, program, programName(program)
    ];
    return content.some(text => text.toLowerCase().includes(query)) || lemmaDetailSearch.matches(query, gap.id);
  });
  const maxPage = Math.max(1, Math.ceil(visibleGaps.length / pageSize));
  lemmaPage = Math.min(lemmaPage, maxPage);
  const offset = (lemmaPage - 1) * pageSize;
  const current = visibleGaps.slice(offset, offset + pageSize);
  lemmaRows.replaceChildren(...(current.length ? current.map(lemmaRow) : [messageRow(strings.empty)]));
  pageRange.textContent = current.length ? strings.pageRange(offset + 1, offset + current.length, visibleGaps.length) : strings.empty;
  previousPage.disabled = lemmaPage === 1;
  nextPage.disabled = lemmaPage === maxPage;
  pageSelect.disabled = maxPage === 1;
  if (pageSelect.options.length !== maxPage) {
    pageSelect.replaceChildren(...Array.from({ length: maxPage }, (_, index) => new Option(index + 1, index + 1)));
  }
  pageSelect.value = String(lemmaPage);
}

function setPage(page) {
  lemmaPage = page;
  renderLemmas();
}

previousPage.addEventListener('click', () => setPage(lemmaPage - 1));
nextPage.addEventListener('click', () => setPage(lemmaPage + 1));
pageSelect.addEventListener('change', () => setPage(Number(pageSelect.value)));

function appendRouteLink(parent, id) {
  const route = gapRoutes.get(id);
  if (route && programs.has(route)) parent.append(anchor(programName(route), '#track-' + route, 'log-note'));
}

function renderLogEntry(run) {
  const article = element('article');
  article.dataset.run = run.run_id + '/' + run.run_attempt;
  const row = element('div', undefined, 'log-entry');
  const judgement = run.verdict === 'ACCEPTED' ? 'accepted' : 'rejected';
  const label = element('div', undefined, 'log-main');
  const meta = element('div', undefined, 'log-meta');
  meta.append(element('span', strings.attempt + ' ' + run.run_attempt + ' · #' + run.run_id, 'log-note'));
  if (run.kind && run.kind !== 'prove') meta.append(element('span', run.kind, 'log-note'));
  const route = gapRoutes.get(run.lemma_id);
  if (route && programs.has(route)) {
    meta.append(element('span', '·', 'log-sep'), anchor(programName(route), '#track-' + route, 'log-note'));
  }
  label.append(element('code', run.lemma_id, 'log-id'), meta);
  row.append(label, verdictTag(strings[judgement], judgement), runLink(run, strings.run));
  article.append(row);
  if (run.agent) {
    const a = run.agent;
    const model = agentName(a.model), harness = agentName(a.harness);
    const version = a.harness_version && a.harness_version !== 'unknown' ? ' ' + a.harness_version : '';
    article.append(element('p', (lang === 'zh' ? '模型：' : 'Model: ') + model +
      ' · Harness: ' + harness + version + ' · ' +
      (a.source === 'self_reported' ? (lang === 'zh' ? '提交者自报' : 'Self-reported') :
        (lang === 'zh' ? '未记录' : 'Unrecorded')), 'log-note agent-attribution'));
  }
  if (run.has_manifest || run.manifest) {
    const details = element('details', undefined, 'manifest');
    const content = element('div');
    details.append(element('summary', strings.manifest), content);
    details.addEventListener('toggle', () => {
      if (!details.open || content.hasChildNodes()) return;
      const params = new URLSearchParams({run: run.run_id, attempt: run.run_attempt});
      loadDisclosure(content,
        () => run.manifest ? Promise.resolve(run) : fetchPublicJson('api/record-manifest?' + params),
        record => content.replaceChildren(element('pre', JSON.stringify(record.manifest, null, 2))));
    });
    article.append(details);
  }
  return article;
}

function renderActivity(event) {
  const item = element('li', undefined, 'activity-item');
  const details = element('div', undefined, 'activity-details');
  const label = Object.hasOwn(strings.activities, event.kind) ? strings.activities[event.kind] : strings.event;
  const byline = element('div', undefined, 'activity-byline');
  byline.append(element('span', event.handle || strings.participant), element('code', event.lemma_id));
  appendRouteLink(byline, event.lemma_id);
  details.append(element('strong', label), byline);

  const links = element('div', undefined, 'activity-links');
  const date = new Date(typeof event.at === 'number' ? event.at * 1000 : event.at);
  if (Number.isFinite(date.getTime())) {
    const timestamp = element('time', eventTime.format(date));
    timestamp.dateTime = date.toISOString();
    links.append(timestamp);
  }
  if (Number.isSafeInteger(event.run_id) && event.run_id > 0) {
    links.append(runLink(event, strings.run));
  } else if (Number.isSafeInteger(event.pr) && event.pr > 0) {
    links.append(anchor(strings.pullRequest + ' ↗', repository + '/pull/' + event.pr, 'evidence-link'));
  }
  item.append(details, links);
  return item;
}

function rankingTimeText(acceptedAt) {
  const age = Math.max(0, Math.floor(Date.now() / 1000 - acceptedAt));
  if (age < 60) return strings.justNow;
  if (age < 3600) return relativeTime.format(-Math.floor(age / 60), 'minute');
  if (age < 86400) return relativeTime.format(-Math.floor(age / 3600), 'hour');
  return relativeTime.format(-Math.floor(age / 86400), 'day');
}

function zhihuUrl(value, kind) {
  if (typeof value !== 'string' || !value) return null;
  let url;
  try {
    url = new URL(value);
  } catch {
    return null;
  }
  if (url.protocol !== 'https:' || url.username || url.password || url.port) return null;
  if (kind === 'avatar') {
    return url.hostname.endsWith('.zhimg.com') ? url.href : null;
  }
  return url.hostname === 'www.zhihu.com' && /^\/people\/[^/]+\/?$/.test(url.pathname)
    ? url.href : null;
}

function renderRankingRow(contributor, index, mode) {
  const item = element('li', undefined, 'ranking-row');
  const rank = element('span', index + 1, 'ranking-position');
  const zhihu = contributor.zhihu;
  const name = typeof zhihu?.name === 'string' ? zhihu.name.trim() : '';
  const avatarUrl = name && zhihuUrl(zhihu.avatar_url, 'avatar');
  const profileUrl = name && zhihuUrl(zhihu.profile_url, 'profile');
  const github = 'https://github.com/' + encodeURIComponent(contributor.handle);
  const githubAvatar = github + '.png?size=64';
  const avatar = element('span', contributor.handle[0].toUpperCase(), 'ranking-avatar');
  avatar.setAttribute('aria-hidden', 'true');
  const photograph = document.createElement('img');
  photograph.alt = '';
  photograph.width = 38;
  photograph.height = 38;
  photograph.loading = 'lazy';
  photograph.referrerPolicy = 'no-referrer';
  photograph.addEventListener('error', () => {
    if (photograph.src === githubAvatar) photograph.remove();
    else photograph.src = githubAvatar;
  });
  photograph.src = avatarUrl || githubAvatar;
  avatar.append(photograph);

  const identity = element('div', undefined, 'ranking-identity');
  if (name) {
    const label = (lang === 'zh' ? '知乎 · ' : 'Zhihu · ') + name;
    identity.append(profileUrl ? anchor(label, profileUrl, 'ranking-name') : element('span', label, 'ranking-name'));
    identity.append(anchor('GitHub · @' + contributor.handle, github, 'ranking-github'));
  } else {
    identity.append(anchor('@' + contributor.handle, github, 'ranking-name'));
  }
  if (Number.isSafeInteger(contributor.latest_accepted_at)) {
    const acceptedAt = contributor.latest_accepted_at;
    const date = new Date(acceptedAt * 1000);
    const time = element('time', rankingTimeText(acceptedAt), 'ranking-time');
    time.dataset.rankTime = String(acceptedAt);
    time.dateTime = date.toISOString();
    time.title = eventTime.format(date);
    identity.append(time);
  }
  const score = renderRankingResult(contributor, strings.rankingPeriods[mode]);
  item.append(rank, avatar, identity, score);
  return item;
}

function renderRankingResult(entry, period) {
  const result = element('div', undefined, 'ranking-result');
  const hasPoints = Number.isSafeInteger(entry.points);
  const score = element('span', '+' + (hasPoints ? entry.points : entry.accepted).toLocaleString(locale), 'ranking-score');
  if (hasPoints) score.append(element('span', strings.pointsUnit, 'ranking-unit'));
  const detail = [];
  if (hasPoints && Number.isSafeInteger(entry.accepted)) detail.push(strings.verifiedCount(entry.accepted));
  if (entry.cuts) detail.push(entry.cuts.toLocaleString(locale) + (lang === 'zh' ? ' 套拆题' : entry.cuts === 1 ? ' cut' : ' cuts'));
  detail.push(period);
  result.append(score, element('span', detail.join(' · '), 'ranking-period'));
  return result;
}

function updateRankingTimes() {
  for (const date of document.querySelectorAll('[data-rank-time]')) {
    date.textContent = rankingTimeText(Number(date.dataset.rankTime));
  }
}

const harnessLabels = {
  "codex": "Codex",
  "claude-code": "Claude Code",
  "cursor": "Cursor",
  "gemini-cli": "Gemini CLI",
  "opencode": "OpenCode",
  "kimi-code": "Kimi Code",
  "minimax-code": "MiniMax Code",
  "zcode": "ZCode",
  "qwen-code": "Qwen Code",
  "qoder": "Qoder",
  "qoder-cn": "Qoder CN",
  "lingma": "通义灵码 / Lingma",
  "trae": "TRAE",
  "codebuddy": "CodeBuddy",
  "comate": "Baidu Comate",
  "codegeex": "CodeGeeX",
  "iflycode": "iFlyCode",
  "github-copilot": "GitHub Copilot",
  "github-copilot-cli": "GitHub Copilot CLI",
  "windsurf": "Windsurf",
  "cline": "Cline",
  "roo-code": "Roo Code",
  "kilo-code": "Kilo Code",
  "continue": "Continue",
  "aider": "Aider",
  "goose": "Goose",
  "openhands": "OpenHands",
  "kiro": "Kiro",
  "amazon-q": "Amazon Q Developer",
  "augment-code": "Augment Code",
  "auggie": "Auggie",
  "devin": "Devin",
  "devin-desktop": "Devin Desktop",
  "jetbrains-ai": "JetBrains AI Assistant",
  "jetbrains-air": "JetBrains Air",
  "junie": "Junie",
  "zed": "Zed",
  "warp": "Warp",
  "tabnine": "Tabnine",
  "replit-agent": "Replit Agent",
  "factory-droid": "Factory Droid",
  "mistral-vibe": "Mistral Vibe",
  "pi": "Pi",
  "antigravity": "Google Antigravity",
  "hermes-agent": "Hermes Agent",
  "swe-agent": "SWE-agent",
  "mini-swe-agent": "mini-SWE-agent",
  "open-interpreter": "Open Interpreter"
};

function agentName(name) {
  if (!name || name === 'unknown') return lang === 'zh' ? '未记录／未知' : 'Unknown / unrecorded';
  if (name === 'other') return lang === 'zh' ? '其他工具' : 'Other tools';
  return Object.hasOwn(harnessLabels, name) ? harnessLabels[name] : name;
}

const SVG_NS = 'http://www.w3.org/2000/svg';
const XLINK_NS = 'http://www.w3.org/1999/xlink';
const BRAND_ICON_KEY = /^[a-z0-9][a-z0-9-]{0,31}$/;
let brandSpritePromise = null;

function ensureBrandSprite() {
  if (brandSpritePromise || document.getElementById('agent-brand-sprite')) return;
  const spriteUrl = document.getElementById('rankings')?.dataset.brandSprite || 'agent-icons.svg';
  brandSpritePromise = fetch(spriteUrl)
    .then(res => (res.ok ? res.text() : ''))
    .then(markup => {
      if (!markup || document.getElementById('agent-brand-sprite')) return;
      const doc = new DOMParser().parseFromString(markup, 'image/svg+xml');
      const parsed = doc.documentElement;
      if (!parsed || parsed.localName !== 'svg' || doc.querySelector('parsererror')) return;
      const svg = document.importNode(parsed, true);
      svg.id = 'agent-brand-sprite';
      svg.setAttribute('aria-hidden', 'true');
      svg.style.position = 'absolute';
      svg.style.width = '0';
      svg.style.height = '0';
      svg.style.overflow = 'hidden';
      svg.style.pointerEvents = 'none';
      document.body.prepend(svg);
    })
    .catch(() => { brandSpritePromise = null; });
}

function agentBrandIcon(entry, kind = 'models') {
  const name = typeof entry === 'string' ? entry : (entry?.name || '');
  let key = entry && typeof entry === 'object' && typeof entry.icon === 'string' && BRAND_ICON_KEY.test(entry.icon)
    ? entry.icon
    : null;
  if (!key && kind === 'providers' && name === 'unknown') key = 'provider-unknown';
  const icon = element('span', key ? '' : name.slice(0, 1).toUpperCase(), 'agent-brand-icon');
  icon.setAttribute('aria-hidden', 'true');
  if (key) {
    ensureBrandSprite();
    icon.classList.add('has-brand');
    const svg = document.createElementNS(SVG_NS, 'svg');
    svg.setAttribute('class', 'agent-brand-svg');
    svg.setAttribute('aria-hidden', 'true');
    const use = document.createElementNS(SVG_NS, 'use');
    use.setAttribute('href', '#brand-' + key);
    use.setAttributeNS(XLINK_NS, 'xlink:href', '#brand-' + key);
    svg.append(use);
    icon.append(svg);
  }
  return icon;
}

function renderAgentRankingRow(entry, index, kind = 'models') {
  const isProvider = kind === 'providers' || kind === true;
  const item = element('li', undefined, 'ranking-row agent-ranking-row');
  const labelText = isProvider && entry.name === 'unknown'
    ? (lang === 'zh' ? '未识别厂商' : 'Unidentified provider')
    : agentName(entry.name);
  const name = element('div', undefined, 'ranking-name agent-brand-name');
  name.append(agentBrandIcon(entry, kind), element('strong', labelText, 'agent-brand-label'));
  if (isProvider && Array.isArray(entry.models) && entry.models.length) {
    const showLabel = lang === 'zh' ? '查看旗下模型' : 'Show models';
    const hideLabel = lang === 'zh' ? '收起旗下模型' : 'Hide models';
    const toggle = element('button', showLabel, 'provider-toggle');
    toggle.type = 'button';
    toggle.setAttribute('aria-expanded', 'false');
    let subList = null;
    toggle.addEventListener('click', () => {
      const expanded = toggle.getAttribute('aria-expanded') === 'true';
      if (!subList) {
        subList = element('ol', undefined, 'ranking-list provider-models-list');
        subList.append(...entry.models.map((m, i) => renderAgentRankingRow(m, i, 'models')));
        item.append(subList);
      }
      subList.hidden = expanded;
      toggle.setAttribute('aria-expanded', String(!expanded));
      toggle.textContent = expanded ? showLabel : hideLabel;
      const scrollBox = item.closest('.ranking-scroll');
      if (scrollBox) updateRankingFade(scrollBox);
    });
    name.append(toggle);
  }
  item.append(element('span', index + 1, 'ranking-position'), name,
    renderRankingResult(entry, strings.rankingPeriods.all_time));
  return item;
}

let agentDimension = 'providers';

function seedRankingFeeds(rankings, agentRankings) {
  rankingsEpoch += 1;
  const setFeed = (key, rows, total) => {
    const items = Array.isArray(rows) ? rows.slice() : [];
    const resolvedTotal = Number.isSafeInteger(total) ? Math.max(total, items.length) : items.length;
    rankingFeeds[key] = {
      items,
      total: resolvedTotal,
      hasMore: items.length < resolvedTotal,
      loading: false,
      epoch: rankingsEpoch,
    };
  };
  setFeed('all_time', rankings?.all_time, rankings?.all_time_total ?? rankings?.contributors);
  setFeed('hour', rankings?.hour, rankings?.hour_total);
  const totals = agentRankings?.totals || {};
  setFeed('providers', agentRankings?.providers, totals.providers);
  setFeed('models', agentRankings?.models, totals.models);
  setFeed('harnesses', agentRankings?.harnesses, totals.harnesses);
}

function updateRankingFade(scrollEl, hasMoreRemote = false) {
  const canScrollDown = scrollEl.scrollHeight - scrollEl.clientHeight - scrollEl.scrollTop > 6;
  scrollEl.classList.toggle('has-more-below', canScrollDown || hasMoreRemote);
}

function mountProgressiveRankings(scrollEl, key, renderRow, emptyText) {
  if (rankingObserver) {
    rankingObserver.disconnect();
    rankingObserver = null;
  }
  if (activeRankingScroll && activeRankingScroll._onRankingScroll) {
    activeRankingScroll.removeEventListener('scroll', activeRankingScroll._onRankingScroll);
    delete activeRankingScroll._onRankingScroll;
  }
  activeRankingScroll = scrollEl;
  const feed = rankingFeeds[key] || { items: [], total: 0, hasMore: false, loading: false, epoch: rankingsEpoch };
  scrollEl.scrollTop = 0;

  if (!feed.items.length && !feed.hasMore) {
    scrollEl.replaceChildren(element('li', emptyText, 'ranking-empty'));
    scrollEl.classList.remove('has-more-below');
    return;
  }

  let rendered = 0;
  const sentinel = element('li', '', 'ranking-sentinel');
  sentinel.setAttribute('aria-hidden', 'true');
  scrollEl.replaceChildren(sentinel);

  function appendLocalBatch() {
    const nextEnd = Math.min(feed.items.length, rendered + RANKINGS_BATCH);
    if (nextEnd <= rendered) return false;
    const frag = document.createDocumentFragment();
    for (let i = rendered; i < nextEnd; i += 1) {
      frag.append(renderRow(feed.items[i], i));
    }
    rendered = nextEnd;
    scrollEl.insertBefore(frag, sentinel);
    if (rendered >= feed.items.length && !feed.hasMore) sentinel.remove();
    updateRankingFade(scrollEl, rendered < feed.items.length || feed.hasMore);
    return true;
  }

  async function ensureMore() {
    if (!scrollEl.isConnected || feed.epoch !== rankingsEpoch) return;
    if (appendLocalBatch()) return;
    if (!feed.hasMore || feed.loading) return;
    feed.loading = true;
    const requestEpoch = feed.epoch;
    const offset = feed.items.length;
    try {
      const response = await fetch(
        'api/rankings?mode=' + encodeURIComponent(key) + '&offset=' + offset + '&limit=' + RANKINGS_BATCH,
        { cache: 'no-store' }
      );
      if (!response.ok) throw new Error('rankings_fetch_failed');
      const page = await response.json();
      if (requestEpoch !== rankingsEpoch || !scrollEl.isConnected) return;
      const incoming = Array.isArray(page.items) ? page.items : [];
      if (offset === feed.items.length && incoming.length) {
        feed.items.push(...incoming);
      }
      if (Number.isSafeInteger(page.total)) feed.total = Math.max(page.total, feed.items.length);
      feed.hasMore = Boolean(page.has_more) && incoming.length > 0 && feed.items.length < feed.total;
      appendLocalBatch();
      if (!feed.hasMore && rendered >= feed.items.length) sentinel.remove();
      updateRankingFade(scrollEl, rendered < feed.items.length || feed.hasMore);
    } catch {
      feed.hasMore = false;
      if (rendered >= feed.items.length) sentinel.remove();
      updateRankingFade(scrollEl, false);
    } finally {
      feed.loading = false;
    }
  }

  appendLocalBatch();
  const onScroll = () => {
    updateRankingFade(scrollEl, rendered < feed.items.length || feed.hasMore);
    if (scrollEl.scrollHeight - scrollEl.clientHeight - scrollEl.scrollTop < 180) {
      ensureMore();
    }
  };
  scrollEl._onRankingScroll = onScroll;
  scrollEl.addEventListener('scroll', onScroll, { passive: true });
  if ('IntersectionObserver' in window && sentinel.isConnected) {
    rankingObserver = new IntersectionObserver(entries => {
      if (entries.some(entry => entry.isIntersecting)) ensureMore();
    }, { root: scrollEl, rootMargin: '180px 0px' });
    rankingObserver.observe(sentinel);
  }
  requestAnimationFrame(() => updateRankingFade(scrollEl, rendered < feed.items.length || feed.hasMore));
}

function renderAgentColumns(container) {
  const labels = lang === 'zh'
    ? {providers: '模型厂商', models: '具体模型', harnesses: 'Harness 工具'}
    : {providers: 'Model providers', models: 'Models', harnesses: 'Harness tools'};
  const controls = element('div', undefined, 'agent-ranking-views');
  const modes = element('div', undefined, 'rankings-modes');
  modes.setAttribute('role', 'group');
  modes.setAttribute('aria-label', lang === 'zh' ? '榜单分类' : 'Leaderboard categories');
  controls.append(modes);
  for (const [key, label] of Object.entries(labels)) {
    const button = element('button', label);
    button.type = 'button';
    button.dataset.agentDimension = key;
    button.setAttribute('aria-pressed', String(key === agentDimension));
    button.onclick = () => {
      agentDimension = key;
      renderRankingMode();
      container.querySelector('[data-agent-dimension="' + key + '"]')?.focus();
    };
    modes.append(button);
  }
  const list = element('ol', undefined, 'ranking-list ranking-scroll');
  list.setAttribute('aria-label', labels[agentDimension]);
  container.replaceChildren(controls, list);
  const empty = agentRankingsData
    ? (lang === 'zh' ? '暂无通过验证的记录。' : 'No verified contributions yet.')
    : strings.rankingsUnavailable;
  mountProgressiveRankings(list, agentDimension, (entry, index) => renderAgentRankingRow(entry, index, agentDimension), empty);
}

function renderRankingMode() {
  if (!rankingsData) return;
  const agents = rankingMode === 'agents';
  const columns = document.getElementById('agent-ranking-columns');
  columns.hidden = !agents;
  rankingsList.hidden = agents;
  document.getElementById('agent-ranking-controls').hidden = !agents;
  document.querySelector('.ranking-candidate').hidden = agents;
  document.getElementById('rankings-summary').textContent = agents
    ? (topic === 'twin-primes'
      ? (lang === 'zh' ? '积分来自首个通过的证明和正式采用的拆题。' : 'Points come from first accepted proofs and adopted cuts.')
      : (lang === 'zh' ? '按本研究台累计首次核验积分排列。旧规则下首次通过的题每道计 1 分。' : 'Ranked by points from first accepted proofs on this research desk. Each first acceptance under the old rules counts for one point.'))
    : topic === 'twin-primes'
      ? (lang === 'zh' ? '贡献榜计入首个通过的证明和正式采用的拆题。' : 'The leaderboard credits first accepted proofs and adopted cuts.')
      : strings.rankingsSummary(rankingsData.contributors.toLocaleString(locale), rankingsData.proofs.toLocaleString(locale));
  if (agents) {
    renderAgentColumns(columns);
    const total = rankingFeeds[agentDimension]?.total ?? 0;
    rankingsAnnouncement.textContent = lang === 'zh' ? '共 ' + total + ' 项。' : total + ' entries.';
  } else {
    const empty = rankingMode === 'hour' ? strings.noHourContributors : strings.noContributors;
    mountProgressiveRankings(rankingsList, rankingMode, (entry, index) => renderRankingRow(entry, index, rankingMode), empty);
    const total = rankingFeeds[rankingMode]?.total ?? 0;
    document.getElementById('ranking-next-place').textContent = String(total + 1);
    rankingsAnnouncement.textContent = strings.rankingsCount(total);
  }
}

function selectRankingMode(mode) {
  rankingMode = mode;
  for (const button of rankingsModes) button.setAttribute('aria-pressed', String(button.dataset.rankingMode === mode));
  renderRankingMode();
}

function renderRankings(rankings, agentRankings) {
  if (!rankings) {
    if (!rankingsData) rankingsList.replaceChildren(element('li', strings.rankingsUnavailable, 'ranking-empty'));
    return;
  }
  const snapshot = JSON.stringify({rankings, agentRankings});
  if (rankingsSnapshot === snapshot) {
    updateRankingTimes();
    return;
  }
  rankingsData = rankings;
  agentRankingsData = agentRankings || null;
  rankingsSnapshot = snapshot;
  seedRankingFeeds(rankings, agentRankings);
  document.getElementById('rankings-summary').textContent = strings.rankingsSummary(
    rankings.contributors.toLocaleString(locale), rankings.proofs.toLocaleString(locale)
  );
  selectRankingMode(rankingMode ?? (rankings.hour.length ? 'hour' : 'all_time'));
}

for (const button of rankingsModes) {
  button.addEventListener('click', () => selectRankingMode(button.dataset.rankingMode));
}

function showDeskNotice(message) {
  if (deskNotice.textContent !== message) deskNotice.textContent = message;
  deskNotice.hidden = !message;
}

function renderDesk(desk) {
  renderRankings(desk?.rankings, desk?.agent_rankings);
  if (!desk) {
    showDeskNotice(lastDesk === null ? strings.deskUnavailable : strings.stale);
    if (lastDesk === null) {
      deskActivity.replaceChildren();
    }
    return;
  }
  showDeskNotice('');
  const snapshot = JSON.stringify(desk);
  if (lastDesk === snapshot) return;
  lastDesk = snapshot;
  document.getElementById('desk-active').textContent = desk.active.toLocaleString(locale);
  document.getElementById('live-hero').textContent = desk.active.toLocaleString(locale);
  document.getElementById('hero-sessions').textContent = desk.sessions.toLocaleString(locale);
  const frontier = document.getElementById('frontier-events');
  frontier.replaceChildren(...desk.activities.slice(0, 2).map(activity => {
    const item = element('div', undefined, 'frontier-entry');
    item.append(element('small', eventTime.format(new Date(activity.at * 1000))),
      element('strong', strings.activities[activity.kind] || strings.event),
      element('code', activity.lemma_id));
    return item;
  }));
  if (!desk.activities.length) frontier.textContent = strings.noActivity;
  document.getElementById('desk-sessions').textContent = desk.sessions.toLocaleString(locale);
  activityItems = desk.activities;
  renderActivityPage();
}

function bindPageInput(input, getCurrent, getTotal, onJump) {
  if (!input) return;
  const commit = () => {
    const raw = input.value.trim();
    const total = Math.max(1, getTotal());
    const parsed = Number.parseInt(raw, 10);
    if (!Number.isFinite(parsed) || !/^[0-9]+$/.test(raw)) {
      input.value = String(getCurrent());
      return;
    }
    const target = Math.max(1, Math.min(total, parsed));
    input.value = String(target);
    if (target !== getCurrent()) onJump(target);
  };
  input.addEventListener('focus', () => input.select());
  input.addEventListener('keydown', event => {
    if (event.key === 'Enter') {
      event.preventDefault();
      commit();
      input.blur();
    } else if (event.key === 'Escape') {
      input.value = String(getCurrent());
      input.blur();
    }
  });
  input.addEventListener('blur', commit);
}

const activityPageSize = 9;
const activityFirst = document.getElementById('activity-first');
const activityPrev = document.getElementById('activity-prev');
const activityNext = document.getElementById('activity-next');
const activityLast = document.getElementById('activity-last');
const activityInput = document.getElementById('activity-input');
const activityTotal = document.getElementById('activity-total');
const activityPageLabel = document.getElementById('activity-page');
let activityItems = [];
let activityPage = 0;

function activityTotalPages() {
  return Math.max(1, Math.ceil(activityItems.length / activityPageSize));
}

function renderActivityPage() {
  const totalPages = activityTotalPages();
  if (activityPage >= totalPages) activityPage = totalPages - 1;
  const start = activityPage * activityPageSize;
  const slice = activityItems.slice(start, start + activityPageSize);
  deskActivity.replaceChildren(...(slice.length
    ? slice.map(renderActivity) : [element('li', strings.noActivity, 'empty-state')]));
  const current = activityPage + 1;
  if (activityFirst) activityFirst.disabled = current <= 1;
  if (activityPrev) activityPrev.disabled = current <= 1;
  if (activityNext) activityNext.disabled = current >= totalPages;
  if (activityLast) activityLast.disabled = current >= totalPages;
  if (activityInput) {
    activityInput.value = String(current);
    activityInput.disabled = totalPages <= 1;
  }
  if (activityTotal) activityTotal.textContent = String(totalPages);
  if (activityPageLabel) {
    activityPageLabel.textContent = lang === 'zh'
      ? '第 ' + current + ' / ' + totalPages + ' 页'
      : 'Page ' + current + ' of ' + totalPages;
  }
}

function goActivityPage(targetPage) {
  const totalPages = activityTotalPages();
  const clamped = Math.max(1, Math.min(totalPages, targetPage));
  activityPage = clamped - 1;
  renderActivityPage();
}

if (activityFirst) activityFirst.addEventListener('click', () => goActivityPage(1));
if (activityPrev) activityPrev.addEventListener('click', () => goActivityPage(activityPage));
if (activityNext) activityNext.addEventListener('click', () => goActivityPage(activityPage + 2));
if (activityLast) activityLast.addEventListener('click', () => goActivityPage(activityTotalPages()));
bindPageInput(activityInput, () => activityPage + 1, activityTotalPages, goActivityPage);

function renderResults(results) {
  const snapshot = JSON.stringify(results);
  if (lastResults === snapshot) return;
  lastResults = snapshot;
  const expanded = new Set(Array.from(
    verificationLog.querySelectorAll('details[open]'), details => details.parentElement.dataset.run
  ));
  const entries = results.map(run => {
    const entry = renderLogEntry(run);
    if (expanded.has(entry.dataset.run)) {
      const manifest = entry.querySelector('details');
      if (manifest) manifest.open = true;
    }
    return entry;
  });
  verificationLog.replaceChildren(...(entries.length ? entries : [element('p', strings.noRecords, 'empty-state')]));
}

// Display 5 records per UI page so the right card naturally matches the left card's height.
const recordPageSize = 5;
const recordFirst = document.getElementById('record-first');
const recordPrev = document.getElementById('record-prev');
const recordNext = document.getElementById('record-next');
const recordLast = document.getElementById('record-last');
const recordInput = document.getElementById('record-input');
const recordTotal = document.getElementById('record-total');
const recordRetry = document.getElementById('record-retry');
const recordStatus = document.getElementById('record-status');
const recordPage = document.getElementById('record-page');
let currentRecordPage = 1;
let totalRecordPages = 1;
let recordLoaded = false;
let recordPending = false;
let recordVisible = false;
let retryRecordPage = 1;
let latestRecordKey = '';
let displayedHead = null;

function syncRecordControls() {
  const locked = recordPending || !recordLoaded;
  if (recordFirst) recordFirst.disabled = locked || currentRecordPage <= 1;
  if (recordPrev) recordPrev.disabled = locked || currentRecordPage <= 1;
  if (recordNext) recordNext.disabled = locked || currentRecordPage >= totalRecordPages;
  if (recordLast) recordLast.disabled = locked || currentRecordPage >= totalRecordPages;
  if (recordInput) {
    recordInput.value = String(currentRecordPage);
    recordInput.disabled = locked || totalRecordPages <= 1;
  }
  if (recordTotal) recordTotal.textContent = String(totalRecordPages);
}

async function loadRecordPage(targetPage) {
  if (recordPending) return;
  const pageNum = Math.max(1, Math.floor(targetPage) || 1);
  const requestedHead = latestRecordKey;
  recordPending = true;
  syncRecordControls();
  if (recordRetry) recordRetry.hidden = true;
  if (recordStatus) recordStatus.hidden = true;
  try {
    const response = await fetch('api/records?view=summary&page=' + encodeURIComponent(String(pageNum)) + '&limit=' + recordPageSize,
      {signal: AbortSignal.timeout(15000)});
    if (!response.ok) throw new Error('Records unavailable');
    const data = await response.json();
    const results = Array.isArray(data.results) ? data.results : [];
    const total = Number.isInteger(data.total) ? data.total : results.length;
    totalRecordPages = Number.isInteger(data.pages) && data.pages > 0
      ? data.pages : Math.max(1, Math.ceil(total / recordPageSize));
    currentRecordPage = Number.isInteger(data.page) && data.page > 0
      ? Math.min(data.page, totalRecordPages) : Math.min(pageNum, totalRecordPages);
    recordLoaded = true;
    if (currentRecordPage === 1) displayedHead = requestedHead;
    renderResults(results);
    if (recordPage) {
      recordPage.textContent = lang === 'zh'
        ? '第 ' + currentRecordPage + ' / ' + totalRecordPages + ' 页'
        : 'Page ' + currentRecordPage + ' of ' + totalRecordPages;
    }
  } catch {
    retryRecordPage = pageNum;
    if (recordRetry) recordRetry.hidden = false;
    if (recordStatus) {
      recordStatus.textContent = strings.failure;
      recordStatus.hidden = false;
    }
  } finally {
    recordPending = false;
    syncRecordControls();
  }
}

if (recordFirst) recordFirst.addEventListener('click', () => loadRecordPage(1));
if (recordPrev) recordPrev.addEventListener('click', () => loadRecordPage(currentRecordPage - 1));
if (recordNext) recordNext.addEventListener('click', () => loadRecordPage(currentRecordPage + 1));
if (recordLast) recordLast.addEventListener('click', () => loadRecordPage(totalRecordPages));
if (recordRetry) recordRetry.addEventListener('click', () => loadRecordPage(retryRecordPage));
bindPageInput(recordInput, () => currentRecordPage, () => totalRecordPages, loadRecordPage);
new IntersectionObserver(([entry]) => {
  recordVisible = entry.isIntersecting;
  if (recordVisible && (!recordLoaded || (currentRecordPage === 1 && displayedHead !== latestRecordKey))) {
    loadRecordPage(1);
  }
}, {rootMargin: '200px'}).observe(verificationLog);

lemmaSearch.addEventListener('input', () => setPage(1));
lemmaState.addEventListener('change', () => setPage(1));

document.addEventListener('keydown', event => {
  if (event.key !== '/' || event.altKey || event.ctrlKey || event.metaKey ||
      lemmaDialog.open || lemmaSearch.disabled || event.target.closest('input, textarea, select, [contenteditable]')) return;
  event.preventDefault();
  lemmaSearch.focus();
});

const exponentPanel = document.getElementById('lpf-record');
const researchNews = document.getElementById('lpf-news');
if (researchNews && typeof researchNews.showModal === 'function') {
  const opener = document.getElementById('lpf-news-open');
  const seenKey = 'quadratic-primes.news.coe-2026-s41cw';
  opener.addEventListener('click', event => {
    event.preventDefault();
    researchNews.showModal();
  });
  researchNews.addEventListener('close', () => {
    try { localStorage.setItem(seenKey, '1'); } catch {}
    opener.focus({preventScroll: true});
  });
  let seen = false;
  try { seen = localStorage.getItem(seenKey) === '1'; } catch {}
  if (!seen) researchNews.showModal();
}

function renderExponent(record) {
  if (!exponentPanel) return;
  const current = document.getElementById('lpf-current');
  const notice = document.getElementById('lpf-notice');
  if (!record?.current) {
    notice.textContent = current.textContent === '—' ? strings.failure : strings.stale;
    return;
  }
  const zh = lang === 'zh';
  current.textContent = record.current.exponent;
  document.getElementById('lpf-target').textContent = record.target;
  document.getElementById('lpf-kind').textContent = record.current.kind === 'external_certificate'
    ? (zh ? '外部有限证书参数 · 无条件解析转移待核验' : 'External finite certificate · unconditional analytic transfer pending')
    : (zh ? '本站已核验的无条件大素因子界' : 'Unconditional large-prime-factor bound verified here');
  const verified = document.getElementById('lpf-verified');
  if (record.verified) {
    const label = (zh ? '本站 Lean 已通过 · α = ' : 'Site Lean proof · α = ') + record.verified.exponent;
    verified.replaceChildren(anchor(label + ' ↗', record.verified.source_url));
  } else {
    verified.textContent = zh ? '本站暂未通过无条件指数证明。' : 'No unconditional exponent proof has passed here yet.';
  }
  notice.textContent = '';
}

const researchMap = (() => {
const root=document.getElementById('research-map-v4');
let tracks=[],gaps=[],T=new Map(),G=new Map(),groups=new Map(),upstream=new Map(),initialized=false;
const endpointId='L-goldbach-binary-pointwise-positivity';
const tr=(zh,en)=>lang==='zh'?zh:en;
const groupOf=g=>topic?('program-'+programOf(g)):(g.track||(g.id===endpointId?'__goal':'__core'));
const goalTitle=()=>topic?document.getElementById('page-title').textContent.trim():tr('强哥德巴赫猜想','Strong Goldbach conjecture');
const esc=s=>String(s??'').replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const palette={foundation:'#a0c6a1',grh:'#9ab9d7',correlation:'#ebc883',exceptions:'#c4acd7'},roleName=lang==='zh'?{target:'待突破',conditional:'条件归约',lemma:'支撑引理',endpoint:'终点'}:{target:'Open target',conditional:'Conditional',lemma:'Supporting lemma',endpoint:'Target'},distance=new Map();
function dist(id,seen=new Set()){if(distance.has(id))return distance.get(id);if(seen.has(id))throw Error('路线存在循环依赖');let next=new Set(seen);next.add(id);let out=T.get(id).feeds||[],d=out.length?1+Math.max(...out.map(x=>dist(x,next))):0;distance.set(id,d);return d}
function closure(id,next){let set=new Set(),stack=[id];while(stack.length){let x=stack.pop();if(set.has(x))continue;set.add(x);for(const v of next(x))stack.push(v)}return set}
let focus=null,hover=null,onlyChain=false,compact=true,horizontal=false,directionChosen=false,field=null,globalFilter='all',savedScrollY=0,currentTrack=null,observer=null,pendingGap=null,expanded=null,localFilter='all',localSearch='',indexMode=false;
const directionKey='goldbach-map-direction',wideDirection=()=>window.innerWidth>=2400;try{const saved=localStorage.getItem(directionKey);if(saved==='horizontal'||saved==='vertical'){horizontal=saved==='horizontal';directionChosen=true}}catch{}if(!directionChosen)horizontal=wideDirection();function syncDirection(){root?.querySelectorAll('[data-direction]').forEach(x=>x.classList.toggle('active',(x.dataset.direction==='horizontal')===horizontal))}syncDirection();
function status(g){if(g.refutation)return g.refutation.status==='verified'?'refuted':'progress';if(g.proved||g.resolved)return 'verified';if(g.claims_closed)return 'closed';if(assigned(g))return 'progress';return g.role==='target'?'target':'available'}
function statusText(g){if(status(g)==='closed')return closedClaimLabel();if(g.refutation){const v=g.refutation.status==='verified';return lang==='zh'?(v?'已证伪':'反证待核验'):(v?'Refuted':'Refutation under review')}if(g.resolved&&!g.proved)return tr('已解决','Resolved');return ({verified:lang==='zh'?'已核查':'Verified',progress:lang==='zh'?'处理中':'In progress',target:lang==='zh'?'待突破':'Open target',available:lang==='zh'?'可领取':'Available'})[status(g)]}
function stateOK(g,v){return v==='all'||(v==='open'&&!g.proved&&!g.resolved&&!g.refutation)||(v==='target'&&g.role==='target'&&!g.proved&&!g.resolved&&!g.refutation)}
function counts(gs){let verified=gs.filter(g=>status(g)==='verified').length;return {verified,progress:gs.filter(g=>status(g)==='progress').length,available:gs.filter(g=>status(g)==='available').length,target:gs.filter(g=>status(g)==='target').length,pct:gs.length?100*verified/gs.length:0}}
function program(t){let c={};for(const g of groups.get(t.id))c[g.program]=(c[g.program]||0)+1;return Object.keys(c).sort((a,b)=>c[b]-c[a])[0]||'foundation'}
function trackSets(id){return {up:closure(id,x=>upstream.get(x)||[]),down:closure(id,x=>T.get(x)?.feeds||[])}}
function scrollRestore(){requestAnimationFrame(()=>{window.scrollTo({top:savedScrollY,behavior:'instant'});requestAnimationFrame(drawBoard)})}
function enterTrack(id,gap){if(!groups.has(id))return;if(!currentTrack)savedScrollY=window.scrollY;pendingGap=gap||null;if(location.hash===`#route=${encodeURIComponent(id)}`){renderRoute();return}location.hash=`route=${encodeURIComponent(id)}`}
function goOverview(){if(currentTrack)location.hash='';else renderRoute()}
function renderRoute(){let wasTrack=currentTrack;let m=location.hash.match(/^#route=(.+)$/),id=m?decodeURIComponent(m[1]):null;if(id&&!groups.has(id))id=null;currentTrack=id;observer?.disconnect();if(id){localFilter='all';localSearch='';indexMode=false;expanded=pendingGap;pendingGap=null;root.querySelector('#map-overview').hidden=true;root.querySelector('#map-route-view').hidden=false;root.querySelector('#map-focusbar').hidden=true;renderTrack();root.scrollIntoView({block:'start',behavior:'instant'});if(expanded)requestAnimationFrame(()=>root.querySelector(`[data-item="${CSS.escape(expanded)}"]`)?.scrollIntoView({block:'center'}));}else{root.querySelector('#map-overview').hidden=false;root.querySelector('#map-route-view').hidden=true;root.querySelector('#map-route-view').innerHTML='';renderBoard();renderFocus();if(wasTrack)scrollRestore()}}
function renderBoard(){let html='';let active=focus||hover,sets=active?trackSets(active):null,board=root.querySelector('#rm-board'),isHorizontal=horizontal&&window.innerWidth>640;board.classList.toggle('horizontal',isHorizontal);board.classList.toggle('chain-horizontal',isHorizontal&&onlyChain&&!!focus);for(let d=0;d<=Math.max(...distance.values());d++){let list=tracks.filter(t=>dist(t.id)===d).filter(t=>!onlyChain||!focus||sets.up.has(t.id)||sets.down.has(t.id)).filter(t=>groups.get(t.id).some(g=>(!field||(topic?programOf(g)===field:g.program===field))&&stateOK(g,globalFilter))).sort((a,b)=>Number(b.id.startsWith('frontier-'))-Number(a.id.startsWith('frontier-'))||a.title[lang].localeCompare(b.title[lang],locale));if(!list.length)continue;html+=`<section class="level" data-depth="${d}"><h3>${lang==='zh'?'第 '+(d+1)+' 层':'Layer '+(d+1)} · ${d===0?tr('直接汇合','Direct convergence'):`${tr('依赖深度','Dependency depth')} ${d}`}</h3><div class="grid count-${Math.min(list.length,4)}">`;for(const t of list){let gs=groups.get(t.id),c=counts(gs),n=gs.filter(g=>g.role==='target'&&!g.proved&&!g.resolved&&!g.refutation).length,muted=active&&!sets.up.has(t.id)&&!sets.down.has(t.id);html+=`<div class="track ${compact?'compact':'full'} ${focus===t.id?'selected':''} ${muted?'dim':''}" data-track="${esc(t.id)}" style="--c:${palette[program(t)]}" tabindex="0" role="button" aria-label="${tr('聚焦','Focus')} ${esc(t.title[lang])}" title="${esc(t.description[lang])}"><div class="track-title"><strong>${esc(t.title[lang])}</strong>${n?`<span class="target-badge">${lang==='zh'?`${n} 待突破`:`${n} open target${n===1?'':'s'}`}</span>`:''}</div>${compact?'':`<span class="description">${esc(t.description[lang])}</span>`}<span class="stats">${tr('已核查 / 全部','Verified / Total')}：${c.verified} / ${gs.length}</span><span class="bar"><i style="width:${c.pct}%"></i></span><button class="enter-small" data-enter="${esc(t.id)}">${tr('查看','View')} ${gs.length} ${tr('条引理','lemmas')} →</button></div>`}html+='</div></section>'}root.querySelector('#rm-levels').innerHTML=html;requestAnimationFrame(drawBoard)}
function drawBoard(){if(currentTrack)return;let board=root.querySelector('#rm-board'),svg=root.querySelector('#rm-board-svg');if(!board||!svg)return;let rect=board.getBoundingClientRect();svg.setAttribute('viewBox',`0 0 ${rect.width} ${rect.height}`);let active=focus||hover,sets=active?trackSets(active):null,isHorizontal=board.classList.contains('horizontal'),center=el=>{let r=el.getBoundingClientRect();return{x:r.left-rect.left+r.width/2,y:r.top-rect.top+r.height/2,left:r.left-rect.left,right:r.right-rect.left,top:r.top-rect.top,bottom:r.bottom-rect.top}},nodes=new Map([...board.querySelectorAll('[data-track]')].map(x=>[x.dataset.track,center(x)])),goal=center(root.querySelector('#rm-goal')),paths='';function edge(a,b,gold,op,from,to){let d;if(isHorizontal){let x1=a.right,x2=b.left-2,span=Math.max(0,x2-x1),lead=Math.min(12,Math.max(6,span*.22)),ex=x2-lead,dx=Math.max(8,(ex-x1)*.5);d=`M ${x1} ${a.y} C ${x1+dx} ${a.y}, ${ex-dx} ${b.y}, ${ex} ${b.y} L ${x2} ${b.y}`}else{let y1=a.top,y2=b.bottom+2,span=Math.max(0,y1-y2),lead=Math.min(12,Math.max(6,span*.22)),ey=y2+lead,dy=Math.max(10,(y1-ey)*.5);d=`M ${a.x} ${y1} C ${a.x} ${y1-dy}, ${b.x} ${ey+dy}, ${b.x} ${ey} L ${b.x} ${y2}`}paths+=`<path data-from="${esc(from)}" data-to="${esc(to)}" d="${d}" stroke="${gold?'#e3c580':'#a0c6a1'}" stroke-width="${active?2:0.85}" stroke-opacity="${op}" fill="none" marker-end="url(#arr-${gold?'gold':'mint'})"/>`}
for(const t of tracks){if(!nodes.has(t.id))continue;for(const f of t.feeds||[]){if(!nodes.has(f))continue;let down=active&&sets.down.has(t.id)&&sets.down.has(f),up=active&&sets.up.has(t.id)&&sets.up.has(f);if(!active||down||up)edge(nodes.get(t.id),nodes.get(f),!!down,active?.95:.2,t.id,f)}if(!(t.feeds||[]).length&&(!active||sets.down.has(t.id)))edge(nodes.get(t.id),goal,!!active,active?.95:.2,t.id,'goal')}
for(const el of board.querySelectorAll('[data-track]')){el.classList.toggle('selected',focus===el.dataset.track);el.classList.toggle('dim',!!active&&!sets.up.has(el.dataset.track)&&!sets.down.has(el.dataset.track))}svg.innerHTML=`<defs><marker id="arr-gold" viewBox="0 0 8 8" refX="8" refY="4" markerWidth="5.5" markerHeight="5.5" orient="auto"><path d="M0 0L8 4L0 8Z" fill="#e3c580"/></marker><marker id="arr-mint" viewBox="0 0 8 8" refX="8" refY="4" markerWidth="5.5" markerHeight="5.5" orient="auto"><path d="M0 0L8 4L0 8Z" fill="#a0c6a1"/></marker></defs>${paths}`}
function setFocus(id){let rebuild=onlyChain;focus=id;hover=null;if(!id)onlyChain=false;if(rebuild)renderBoard();else drawBoard();renderFocus()}
function renderFocus(){let bar=root.querySelector('#map-focusbar');bar.hidden=!focus||!!currentTrack;if(bar.hidden)return;let t=T.get(focus),up=upstream.get(focus)||[],down=t.feeds||[],buttons=a=>a.map(x=>`<button class="flow-focus" data-focus="${esc(x)}">${esc(T.get(x).title[lang])}</button>`).join('、'),summarize=a=>a.length>3?`${buttons(a.slice(0,3))} ${lang==='zh'?'等 '+a.length+' 条':'and '+a.length+' total'}`:buttons(a);bar.innerHTML=`<div class="focus-inner"><div class="focus-copy"><div class="flowline">${up.length?`${summarize(up)} → `:''}<b>${lang==='zh'?`【当前：${esc(t.title[lang])}】`:`Current: ${esc(t.title[lang])}`}</b>${down.length?` → ${summarize(down)}`:''} → ${esc(goalTitle())}</div></div><div class="focus-actions"><button id="chain-toggle" aria-pressed="${onlyChain}">${onlyChain?tr('显示全部路线','Show all routes'):tr('仅看相关链路','Related routes only')}</button><button data-enter="${esc(focus)}" class="primary">${tr('查看','View')} ${groups.get(focus).length} ${tr('条引理','lemmas')} →</button><button id="clear-focus">${tr('取消聚焦','Clear focus')}</button></div></div>`}
function gapGraph(id){let all=groups.get(id),set=new Set(all.map(g=>g.id)),parents=new Map(all.map(g=>[g.id,[]])),depths=new Map();for(const g of all)for(const d of g.depends_on||[])if(set.has(d))parents.get(d).push(g.id);function depth(g,seen=new Set()){if(depths.has(g.id))return depths.get(g.id);if(seen.has(g.id))return 0;let ns=new Set(seen);ns.add(g.id);let ds=(g.depends_on||[]).filter(x=>set.has(x)).map(x=>depth(G.get(x),ns));let n=ds.length?1+Math.max(...ds):0;depths.set(g.id,n);return n}all.forEach(g=>depth(g));return {set,parents,depths,hasEdges:all.some(g=>(g.depends_on||[]).some(x=>set.has(x)))}}
function gapRelated(id,graph){if(!id)return new Set();let a=closure(id,x=>(G.get(x)?.depends_on||[]).filter(d=>graph.set.has(d))),b=closure(id,x=>graph.parents.get(x)||[]);return new Set([...a,...b])}
function ordered(id,graph){let rank=g=>g.role==='target'?2:g.role==='conditional'?1:0;return [...groups.get(id)].sort((a,b)=>rank(b)-rank(a)||graph.depths.get(b.id)-graph.depths.get(a.id)||a.id.localeCompare(b.id,undefined,{numeric:true}))}
function details(g) {
  return '<div class="detail-inline" data-task-detail>' +
    '<code>' + esc(g.id) + '</code></div>';
}

function resolvedDetails(g){let parents=gaps.filter(x=>(x.depends_on||[]).includes(g.id)),links=ids=>ids.length?ids.map(id=>`<button data-gap-jump="${esc(id)}">${esc(id)}</button>`).join(' · '):tr('无','None');return `<div class="detail-inline"><div class="detail-title"><b>${esc(g.id)}</b><span class="state ${status(g)}">● ${statusText(g)}</span><span class="role">${esc(roleName[g.role]||tr('命题','Statement'))}</span></div><p>${esc(g.plain_statement?.[lang]||tr('无中文说明','No statement available'))}</p>${g.brief?.[lang]?`<p class="muted">${esc(g.brief[lang])}</p>`:''}<div class="related"><b>${tr('上游依赖：','Prerequisites: ')}</b>${links(g.depends_on||[])}<br><b>${tr('下游影响：','Supports: ')}</b>${links(parents.map(x=>x.id))}</div><p class="muted">${tr('文件路径：','File: ')}${esc(g.file||tr('未指定','Not specified'))}</p><b>${tr('Lean 表述','Lean statement')}</b>${g.latest?runLink(g.latest,strings.latestRun).outerHTML:''}${g.refutation?` <a href="${repository}/pull/${Number(g.refutation.pr)}">${statusText(g)} · PR #${Number(g.refutation.pr)}</a>`:''}${g.source && /^https?:\/\//i.test(g.source)?` <a href="${esc(g.source)}" rel="noopener noreferrer">${tr('阅读来源 ↗','Read source ↗')}</a>`:''}<pre>${esc(g.statement||tr('未提供','Not provided'))}</pre>${cutEvidence(g).outerHTML}</div>`}
const trackDetailSearch = detailSearch('brief', () => {
  if (currentTrack) renderTrackPreservingSearch();
});

function renderTrackPreservingSearch() {
  const active = root.querySelector('#track-search');
  if (document.activeElement !== active) {
    renderTrack();
    return;
  }
  const { selectionStart: start, selectionEnd: end } = active;
  renderTrack();
  const input = root.querySelector('#track-search');
  input?.focus({ preventScroll: true });
  if (input && start !== null) input.setSelectionRange(start, end);
}

function renderTrack(){if(!currentTrack)return;observer?.disconnect();trackDetailSearch.update(localSearch.trim().toLowerCase());let id=currentTrack,t=T.get(id),all=groups.get(id),graph=gapGraph(id),ct=counts(all),q=localSearch.trim().toLowerCase(),related=gapRelated(expanded,graph),shown=ordered(id,graph).filter(g=>stateOK(g,localFilter==='chain'?'all':localFilter)&&(!q||`${g.id} ${g.plain_statement?.[lang]||''}`.toLowerCase().includes(q)||trackDetailSearch.matches(q,g.id))&&(localFilter!=='chain'||related.has(g.id))),toButton=(x)=>`<button data-nav="${esc(x)}">${esc(T.get(x).title[lang])}</button>`,feed=t?.feeds||[],ups=upstream.get(id)||[];
let toolbar=[['all',`${tr('全部','All')} ${all.length}`],['open',tr('仅未通过','Not verified')],['target',tr('仅待突破','Open targets')],...(graph.hasEdges?[['chain',tr('仅依赖链','Dependency chain')]]:[])].map(([k,v])=>`<button data-filter="${k}" class="${localFilter===k?'active':''}">${v}</button>`).join('');
let rows=shown.map(g=>`<div class="item status-${status(g)}" data-item="${esc(g.id)}"><div class="row ${expanded===g.id?'active':''}" data-row="${esc(g.id)}" role="button" tabindex="0" aria-expanded="${expanded===g.id}"><span class="lemma-id" title="${esc(g.id)}">${esc(g.id.replace(/^L-goldbach-/,''))}</span><span class="state ${status(g)}">● ${statusText(g)}</span><span class="role">${esc(roleName[g.role]||tr('命题','Statement'))}</span><span class="statement">${esc(g.plain_statement?.[lang]||g.brief?.[lang]||tr('无中文说明','No statement available'))}</span><span class="expand">${expanded===g.id?tr('收起 ▴','Collapse ▴'):tr('展开 ▾','Expand ▾')}</span></div>${expanded===g.id?details(g):''}</div>`).join('');
let chips=shown.map(g=>`<button data-index="${esc(g.id)}" class="index-chip ${status(g)} ${expanded===g.id?'selected':''}" title="${esc(g.id)}"><span>●</span> ${esc(g.id.replace(/^L-goldbach-/,''))}</button>`).join('');
root.querySelector('#map-route-view').innerHTML=`<div class="backbar"><button id="back-overview">← ${tr('返回研究地图','Back to research map')}</button><span class="breadcrumb">${esc(goalTitle())} / ${t?`${lang==='zh'?'第 '+(dist(id)+1)+' 层':'Layer '+(dist(id)+1)} / ${esc(t.title[lang])}`:(id==='__goal'?tr('主命题','Main statement'):tr('核心主干引理','Core lemmas'))}</span></div><div class="track-header"><div class="header-info"><h1>${esc(t?.title[lang]||(id==='__goal'?tr('强哥德巴赫猜想','Strong Goldbach conjecture'):tr('核心主干引理','Core lemmas')))} <small>（${all.length} ${tr('条','lemmas')}）</small></h1><p>${esc(t?.description[lang]||(id==='__goal'?tr('查看主命题的正式表述。','Read the formal statement.'):tr('支撑研究地图的早期核心命题。','Early statements supporting the research map.')))}</p><div class="track-flows">${ups.length?`<span>${tr('上游路线：','Upstream: ')}</span>${ups.map(toButton).join(' ')}`:''}${feed.length?`<span>${tr('流向：','Feeds into: ')}</span>${feed.map(toButton).join(' ')}`:(t?`<span>${tr('流向：','Feeds into: ')}${esc(goalTitle())} →</span>`:'')}</div></div><div class="header-progress"><span>${tr('已核查 / 全部','Verified / Total')}</span><b>${ct.verified} / ${all.length}</b><div class="bar"><i style="width:${ct.pct}%"></i></div><div class="legend"><span class="verified">● ${tr('已核查','Verified')} ${ct.verified}</span><span class="target">● ${tr('待突破','Open targets')} ${ct.target}</span><span class="available">● ${tr('未通过','Not verified')} ${ct.progress+ct.available}</span></div></div></div><section class="track-content"><div class="toolbar">${toolbar}<input id="track-search" type="search" placeholder="${tr('路线内搜索编号或中文命题','Search ID or statement')}" value="${esc(localSearch)}"><div class="segments"><button data-view="list" class="${!indexMode?'active':''}">${tr('列表','List')}</button><button data-view="index" ${graph.hasEdges?`disabled title="${tr('该路线包含依赖关系','This route has dependencies')}"`:''} class="${indexMode?'active':''}">${tr('紧凑索引','Compact index')}</button></div></div><div class="countline">${tr('共','Total')} ${all.length} · ${tr('当前显示','shown')} ${shown.length}</div>${shown.length?(indexMode&&!graph.hasEdges?`<div class="index-area">${expanded&&shown.some(g=>g.id===expanded)?`<div class="index-detail" data-item="${esc(expanded)}">${details(G.get(expanded))}</div>`:''}<div class="index-grid">${chips}</div></div>`:`<div class="proof ${graph.hasEdges?'has-rail':''}">${graph.hasEdges?`<div class="rail"><svg aria-label="${tr('路线内真实依赖关系','Dependencies within this route')}"></svg></div>`:''}<div class="listing"><div class="table-head"><span>${tr('引理编号','Lemma ID')}</span><span>${tr('状态','Status')}</span><span>${tr('角色','Role')}</span><span>${tr('引理陈述','Statement')}</span><span>${tr('操作','Action')}</span></div><div class="items">${rows}</div></div></div>`):`<p class="empty">${tr('没有匹配的命题；请选择全部或清除搜索。','No matches; clear the search or filters.')}</p>`}</section>`;
const detailTarget = root.querySelector('[data-task-detail]');
if (detailTarget) {
  const summary = G.get(expanded);
  loadDisclosure(detailTarget, () => loadTaskDetail(summary.id),
    detail => { detailTarget.outerHTML = resolvedDetails({ ...summary, ...detail }); });
}
if(graph.hasEdges&&shown.length&&!indexMode){let container=root.querySelector('.items');observer=new ResizeObserver(()=>drawRail(id));observer.observe(container);for(const item of container.children)observer.observe(item);requestAnimationFrame(()=>drawRail(id))}}
function drawRail(id){if(id!==currentTrack)return;let rail=root.querySelector('.rail'),svg=rail?.querySelector('svg'),container=root.querySelector('.items');if(!svg||!container)return;let graph=gapGraph(id),items=[...container.querySelectorAll('.item')],map=new Map(items.map((it,i)=>{let row=it.querySelector('.row').getBoundingClientRect(),base=rail.getBoundingClientRect();return [it.dataset.item,{y:row.top+row.height/2-base.top,index:i}]})),w=rail.clientWidth,h=container.offsetHeight+(container.getBoundingClientRect().top-rail.getBoundingClientRect().top),orderedAll=ordered(id,graph),assigned=new Map(),xFor=i=>12+(w-28)*i/4;for(const [i,g] of orderedAll.entries()){let ps=graph.parents.get(g.id)||[],parent=ps.find(x=>assigned.has(x)),siblings=parent?(G.get(parent).depends_on||[]).filter(x=>graph.set.has(x)):[],j=siblings.indexOf(g.id);assigned.set(g.id,g.role==='target'||g.role==='endpoint'?4:parent&&j===0?assigned.get(parent):(graph.depths.get(g.id)+Math.max(0,j)+i)%4)}for(const [id,n] of map)n.x=xFor(assigned.get(id));let rel=gapRelated(expanded,graph),paths='';for(const [key,n] of map)for(const dep of G.get(key).depends_on||[])if(map.has(dep)){let a=map.get(dep),b=n,mid=(a.y+b.y)/2,on=rel.has(key)&&rel.has(dep);paths+=`<path data-from="${esc(dep)}" data-to="${esc(key)}" d="M${a.x} ${a.y} L${a.x} ${mid} C${a.x} ${mid-10},${b.x} ${mid+10},${b.x} ${mid} L${b.x} ${b.y}" stroke="${on?'#e3c580':'#a4b9a5'}" stroke-opacity="${expanded&&!on?.2:.75}" stroke-width="${on?2:1}" fill="none"/>`}
for(const [key,n] of map){let target=G.get(key).role==='target';if(key===expanded)paths+=`<path d="M${n.x} ${n.y}H${w}" stroke="#e3c580" stroke-width="1.5"/>`;if(target)paths+=`<circle cx="${n.x}" cy="${n.y}" r="8" fill="#183126" stroke="#e3c580"/><path d="M${n.x} ${n.y-9}v-8 m-3 3 3-3 3 3" fill="none" stroke="#e3c580"/>`;paths+=`<circle data-node="${esc(key)}" cx="${n.x}" cy="${n.y}" r="${target?5:3.5}" fill="${rel.has(key)||target?'#e3c580':'#d8e5d8'}"/>`}rail.style.height=h+'px';svg.style.height=h+'px';svg.setAttribute('viewBox',`0 0 ${w} ${h}`);svg.innerHTML=paths}
function expandGap(id){expanded=expanded===id?null:id;let old=window.scrollY;renderTrack();window.scrollTo({top:old,behavior:'instant'})}
function jumpGap(id){let g=G.get(id);if(!g)return;let tid=groupOf(g);if(currentTrack!==tid){enterTrack(tid,id);return}localFilter='all';localSearch='';expanded=id;renderTrack();requestAnimationFrame(()=>root.querySelector(`[data-item="${CSS.escape(id)}"]`)?.scrollIntoView({block:'center',behavior:'smooth'}))}
root.addEventListener('click',e=>{let el=e.target.closest('button,[data-track],[data-row],[data-goal]');if(!el){if(e.target.closest('#rm-board')&&focus)setFocus(null);return}if(el.dataset.goal&&!topic){enterTrack('__goal',endpointId);return}if(el.dataset.direction){horizontal=el.dataset.direction==='horizontal';directionChosen=true;try{localStorage.setItem(directionKey,el.dataset.direction)}catch{}syncDirection();renderBoard();return}if(el.dataset.cards){compact=el.dataset.cards==='compact';root.querySelectorAll('[data-cards]').forEach(x=>x.classList.toggle('active',x===el));renderBoard();return}if(el.dataset.focus){setFocus(el.dataset.focus);return}if(el.id==='clear-focus'){setFocus(null);return}if(el.id==='chain-toggle'){onlyChain=!onlyChain;renderBoard();renderFocus();return}if(el.id==='back-overview'){goOverview();return}if(el.dataset.enter){enterTrack(el.dataset.enter);return}if(el.dataset.nav){enterTrack(el.dataset.nav);return}if(el.dataset.gapJump){jumpGap(el.dataset.gapJump);return}if(el.dataset.resultGap){enterTrack(groupOf(G.get(el.dataset.resultGap)),el.dataset.resultGap);return}if(el.dataset.resultTrack){enterTrack(el.dataset.resultTrack);return}if(el.dataset.program)return;if(el.dataset.filter){localFilter=el.dataset.filter;if(localFilter==='chain'&&!expanded){let g=ordered(currentTrack,gapGraph(currentTrack)).find(g=>g.role==='target')||groups.get(currentTrack)[0];expanded=g.id}renderTrack();return}if(el.dataset.view){indexMode=el.dataset.view==='index';renderTrack();return}if(el.dataset.index){expandGap(el.dataset.index);return}if(el.dataset.row){expandGap(el.dataset.row);return}if(el.dataset.track){setFocus(el.dataset.track);return}});
root.addEventListener('dblclick',e=>{let el=e.target.closest('[data-track]');if(el&&!e.target.closest('button'))enterTrack(el.dataset.track)});root.addEventListener('keydown',e=>{if((e.key==='Enter'||e.key===' ')&&e.target.matches('[data-track],[data-row],[data-goal]')){e.preventDefault();e.target.click()}});
root.addEventListener('pointerover',e=>{let card=e.target.closest('[data-track]');if(card&&!focus&&hover!==card.dataset.track){hover=card.dataset.track;drawBoard()}});root.addEventListener('pointerout',e=>{let card=e.target.closest('[data-track]');if(card&&!focus&&!card.contains(e.relatedTarget)){hover=null;drawBoard()}});
root.querySelector('#rm-state').addEventListener('change',e=>{globalFilter=e.target.value;renderBoard()});root.addEventListener('input',e=>{if(e.target.id==='track-search'){localSearch=e.target.value;renderTrackPreservingSearch()}if(e.target.id==='rm-search'){let q=e.target.value.trim().toLowerCase(),box=root.querySelector('#rm-search-results');if(!q){box.innerHTML='';return}let ts=tracks.filter(t=>`${t.id} ${t.title[lang]}`.toLowerCase().includes(q)),gs=gaps.filter(g=>`${g.id} ${g.plain_statement?.[lang]||''}`.toLowerCase().includes(q));box.innerHTML=`<span>${ts.length} ${tr('条路线','routes')} · ${gs.length} ${tr('条命题匹配','matching lemmas')}:</span>`+ts.map(t=>`<button data-result-track="${esc(t.id)}">${esc(t.title[lang])}</button>`).join(' ')+gs.map(g=>`<button data-result-gap="${esc(g.id)}">${esc(g.id)}</button>`).join(' ')}});
window.addEventListener('hashchange',()=>{if(initialized)renderRoute()});window.addEventListener('resize',()=>{if(!directionChosen&&horizontal!==wideDirection()){horizontal=wideDirection();syncDirection()}if(currentTrack)drawRail(currentTrack);else if(horizontal!==root.querySelector('#rm-board')?.classList.contains('horizontal')&&window.innerWidth>640||horizontal&&window.innerWidth<=640&&root.querySelector('#rm-board')?.classList.contains('horizontal'))renderBoard();else drawBoard()});


function update(data, incoming){
 const prevTrack=currentTrack,active=document.activeElement,activeId=active?.id,activeRow=active?.dataset?.row,activeIndex=active?.dataset?.index,activeFilter=active?.dataset?.filter,caret=active?.selectionStart,scrollY=window.scrollY;
 gaps=data;tracks=incoming.length?incoming:[...programs.keys()].map(key=>({id:'program-'+key,title:{zh:programName(key),en:programName(key)},description:{zh:'查看该研究方向的命题。',en:'Explore statements in this research area.'},feeds:[]}));
 T=new Map(tracks.map(t=>[t.id,t]));G=new Map(gaps.map(g=>[g.id,g]));groups=new Map(tracks.map(t=>[t.id,[]]));groups.set('__core',[]);groups.set('__goal',[]);
 for(const g of gaps){let key=groupOf(g);if(!groups.has(key))key='__core';groups.get(key).push(g)}
 upstream=new Map(tracks.map(t=>[t.id,[]]));for(const t of tracks)for(const f of t.feeds||[])upstream.get(f)?.push(t.id);distance.clear();tracks.forEach(t=>dist(t.id));
 const goal=root.querySelector('#rm-goal');goal.innerHTML=topic?`<strong>${esc(goalTitle())}</strong>`:`<strong>${esc(tr('强哥德巴赫猜想 · 每个偶数 n ≥ 4 可表为 p + q','Strong Goldbach conjecture · every even n ≥ 4 is p + q'))}</strong><small>${tracks.length} ${tr('条研究路线','research routes')} · ${gaps.length} ${tr('条命题','statements')}</small><button class="goal-core" data-enter="__core">${tr('核心主干引理','Core lemmas')} (${groups.get('__core').length}) ↗</button>`;
 if(!topic){goal.dataset.goal='1';goal.tabIndex=0}else{delete goal.dataset.goal;goal.removeAttribute('tabindex')}
 if(!initialized){initialized=true;renderRoute();return}
 if(prevTrack&&groups.has(prevTrack)){currentTrack=prevTrack;renderTrack();{const selector=activeId?'#'+CSS.escape(activeId):activeRow?`[data-row="${CSS.escape(activeRow)}"]`:activeIndex?`[data-index="${CSS.escape(activeIndex)}"]`:activeFilter?`[data-filter="${CSS.escape(activeFilter)}"]`:null;const e=selector&&root.querySelector(selector);if(e){e.focus({preventScroll:true});if(typeof caret==='number'&&e.setSelectionRange)e.setSelectionRange(caret,caret)}}}else{renderBoard();renderFocus()}
 window.scrollTo({top:scrollY,behavior:'instant'});
}
return {update,setProgram(value){field=value;if(initialized&&!currentTrack)renderBoard()}};
})();

let cachedTracks = [];
let cachedRevision;

async function loadStatus() {
  if (loading || document.hidden) return;
  loading = true;
  const request = new AbortController();
  const timeout = window.setTimeout(() => request.abort(), 30000);
  try {
    const incremental = lastGaps !== null;
    const response = await fetch(incremental ? 'api/status?view=board-index-delta-gzip' : 'api/status?view=board-index-gzip', {
      headers: { Accept: 'application/json' },
      signal: request.signal,
    });
    if (!response.ok) throw new Error('Status request failed');
    const data = await response.json();
    const { counts, results, desk, lpf_record, catalogue_revision } = data;
    if (incremental && cachedRevision !== catalogue_revision) {
      window.location.reload();
      return;
    }
    const previous = incremental ? new Map(publishedGaps.map(gap => [gap.id, gap])) : null;
    const gaps = previous ? data.gaps.map(gap => ({ ...previous.get(gap.id), ...gap })) : data.gaps;
    const tracks = incremental ? cachedTracks : (data.tracks || []);
    cachedTracks = tracks;
    cachedRevision = catalogue_revision;
    const pageRevision = document.querySelector('meta[name="catalogue-revision"]')?.content;
    if (pageRevision && catalogue_revision && pageRevision !== catalogue_revision) {
      window.location.reload();
      return;
    }
    renderExponent(lpf_record);
    assignments = desk?.assignments ?? assignments;
    document.getElementById('hero-available').textContent = gaps.filter(canClaim).length;
    const latest = results[0];
    document.getElementById('news-verdict').textContent = latest
      ? latest.lemma_id + (latest.kind && latest.kind !== 'prove' ? ' · ' + latest.kind : '') + ' · ' + (latest.verdict === 'ACCEPTED' ? strings.accepted : strings.rejected)
      : strings.noRecords;
    const gapsSnapshot = JSON.stringify([gaps, tracks, assignments]);
    if (lastGaps !== gapsSnapshot) {
      publishedGaps = gaps;
      gapRoutes = new Map(gaps.map(gap => [gap.id, programOf(gap)]));
      updateRouteActivity(gaps);
      researchMap.update(gaps, tracks);
      renderProgramCounts();
      renderLemmas();
      if (lemmaDialog.open) renderGapDetail();
      if (lastGaps === null) {
        const requested = new URLSearchParams(window.location.search).get('lemma');
        if (requested && gaps.some(gap => gap.id === requested)) openGap(requested);
      }
      lastGaps = gapsSnapshot;
    }
    lemmaSearch.disabled = false;
    lemmaState.disabled = false;
    for (const name of ['accepted', 'open', 'published', 'attempts']) {
      document.getElementById('count-' + name).textContent = counts[name].toLocaleString(locale);
    }
    const proofProgress = document.getElementById('proof-progress');
    if (proofProgress) {
      proofProgress.max = Math.max(1, counts.published);
      proofProgress.value = counts.accepted;
      document.getElementById('proof-progress-caption').textContent =
        counts.accepted.toLocaleString(locale) + ' / ' + counts.published.toLocaleString(locale);
    }
    latestRecordKey = latest ? latest.run_id + '/' + latest.run_attempt : '';
    if (recordVisible && (!recordLoaded || (currentRecordPage === 1 && displayedHead !== latestRecordKey))) {
      loadRecordPage(1);
    }
    renderDesk(desk);
  } catch {
    renderExponent(null);
    if (lastGaps === null) {
      lemmaRows.replaceChildren(messageRow(strings.failure, anchor(strings.published, repository + '/blob/main/research/' + (topic ? 'problems.json' : 'gaps.json'))));
      lemmaSearch.disabled = true;
      lemmaState.disabled = true;
    }
    renderDesk(null);
  } finally {
    window.clearTimeout(timeout);
    loading = false;
  }
}

function bindPromptCopy(button, prompt, announcement, manualMessage = strings.copyManual) {
  const label = button.textContent;
  let reset;
  button.addEventListener('click', async () => {
    try {
      await navigator.clipboard.writeText(prompt.textContent);
      button.textContent = strings.copied;
      announcement.textContent = strings.copied;
      window.clearTimeout(reset);
      reset = window.setTimeout(() => {
        button.textContent = label;
        announcement.textContent = '';
      }, 1900);
    } catch {
      const disclosure = prompt.closest('details');
      if (disclosure) disclosure.open = true;
      const range = document.createRange();
      range.selectNodeContents(prompt);
      const selection = window.getSelection();
      selection.removeAllRanges();
      selection.addRange(range);
      announcement.textContent = manualMessage;
    }
  });
}

bindPromptCopy(
  document.getElementById('copy-prompt'),
  document.getElementById('agent-prompt'),
  document.getElementById('copy-announcement')
);

const rankingsPrompt = document.getElementById('rankings-prompt');
rankingsPrompt.textContent = document.getElementById('agent-prompt').textContent;
bindPromptCopy(
  document.getElementById('copy-rankings'),
  rankingsPrompt,
  document.getElementById('rankings-copy-announcement')
);

const participation = document.getElementById('participation');
if (participation) {
  const prompt = document.getElementById('participation-prompt');
  prompt.textContent = document.getElementById('agent-prompt').textContent;
  bindPromptCopy(
    document.getElementById('copy-participation-prompt'),
    prompt,
    document.getElementById('participation-copy-announcement')
  );
  bindPromptCopy(
    document.getElementById('copy-github-auth'),
    document.getElementById('github-auth-command'),
    document.getElementById('github-auth-announcement'),
    '请复制已选中的命令。'
  );

  const source = new URLSearchParams(window.location.search).get('from');
  const referrerHost = document.referrer ? new URL(document.referrer).hostname : '';
  if (source === 'zhihu' || referrerHost === 'zhihu.com' || referrerHost.endsWith('.zhihu.com')) {
    participation.open = true;
  }
  const openParticipationAnchor = () => {
    if (window.location.hash === '#participation') {
      participation.open = true;
      participation.scrollIntoView();
    }
  };
  openParticipationAnchor();
  window.addEventListener('hashchange', openParticipationAnchor);
}

function initSponsorMarquee() {
  const grid = document.querySelector('.sponsor-wall .sponsor-grid');
  if (!grid) return;
  const originals = Array.from(grid.children).filter(node => node.tagName === 'FIGURE');
  if (originals.length < 4) return;

  const prepCard = card => {
    for (const el of card.querySelectorAll('a, img')) {
      el.draggable = false;
      if (el.tagName === 'IMG') el.loading = 'eager';
    }
    return card;
  };
  originals.forEach(prepCard);

  const reducedMotion = window.matchMedia('(prefers-reduced-motion: reduce)');
  const BASE_SPEED = 20; // px/s gentle drift
  let rafId = 0;
  let lastFrame = 0;
  let lastWidth = 0;
  let isMarquee = false;
  let stage = null;
  let tracks = [];
  let cycles = [0, 0];
  let offsets = [0, 0];
  let staggered = false;
  let velocity = 0;
  let resumeAt = 0;
  let hovered = false;
  let focusedWithin = false;
  let dragging = false;
  let inViewport = true;
  let activePointer = null;
  let startX = 0;
  let lastX = 0;
  let lastMoveTime = 0;
  let dragMoved = false;
  let suppressClickUntil = 0;

  const wrap = (value, cycle) => (cycle > 0 ? ((value % cycle) + cycle) % cycle : 0);

  function renderTracks() {
    for (let i = 0; i < tracks.length; i++) {
      const pos = wrap(offsets[i], cycles[i]);
      tracks[i].style.transform = 'translate3d(' + (-pos).toFixed(2) + 'px, 0, 0)';
    }
  }

  function step(now) {
    rafId = 0;
    if (!isMarquee) return;
    const dt = lastFrame ? Math.min(0.05, Math.max(0, (now - lastFrame) / 1000)) : 0;
    lastFrame = now;
    if (dt > 0 && !dragging && inViewport && !document.hidden) {
      if (Math.abs(velocity) > 2) {
        const delta = velocity * dt;
        offsets[0] += delta;
        offsets[1] += delta;
        velocity *= Math.exp(-dt * 5.5);
      } else {
        velocity = 0;
        if (!hovered && !focusedWithin && !reducedMotion.matches && now >= resumeAt) {
          const delta = BASE_SPEED * dt;
          offsets[0] += delta;
          offsets[1] += delta;
        }
      }
      renderTracks();
    }
    rafId = window.requestAnimationFrame(step);
  }

  function startLoop() {
    if (!rafId && isMarquee) {
      lastFrame = 0;
      rafId = window.requestAnimationFrame(step);
    }
  }

  function stopLoop() {
    if (rafId) {
      window.cancelAnimationFrame(rafId);
      rafId = 0;
    }
  }

  function measureSingleRowWidth() {
    const probe = document.createElement('div');
    probe.style.cssText = 'position:absolute;left:-99999px;top:0;visibility:hidden;display:flex;flex-wrap:nowrap;gap:.5rem;pointer-events:none;width:max-content;';
    for (const card of originals) probe.append(card.cloneNode(true));
    grid.append(probe);
    const width = probe.scrollWidth;
    probe.remove();
    return width;
  }

  function populateTrack(track, items, viewportWidth) {
    track.replaceChildren();
    for (const item of items) track.append(item);
    // Append one clone set first so we can measure exact cycle distance including CSS gap.
    const firstClones = items.map(item => {
      const clone = prepCard(item.cloneNode(true));
      clone.setAttribute('aria-hidden', 'true');
      for (const link of clone.querySelectorAll('a')) link.tabIndex = -1;
      return clone;
    });
    for (const clone of firstClones) track.append(clone);
    const cycleWidth = firstClones[0].offsetLeft - items[0].offsetLeft;
    if (cycleWidth <= 0) return 0;
    const totalCopies = Math.min(12, Math.max(3, Math.ceil((viewportWidth + cycleWidth * 2) / cycleWidth)));
    for (let c = 2; c < totalCopies; c++) {
      for (const item of items) {
        const clone = prepCard(item.cloneNode(true));
        clone.setAttribute('aria-hidden', 'true');
        for (const link of clone.querySelectorAll('a')) link.tabIndex = -1;
        track.append(clone);
      }
    }
    return cycleWidth;
  }

  function mountStatic() {
    stopLoop();
    isMarquee = false;
    stage = null;
    tracks = [];
    cycles = [0, 0];
    grid.classList.remove('is-marquee');
    grid.replaceChildren(...originals);
  }

  function mountMarquee(viewportWidth) {
    const prevRatios = [
      cycles[0] > 0 ? wrap(offsets[0], cycles[0]) / cycles[0] : 0,
      cycles[1] > 0 ? wrap(offsets[1], cycles[1]) / cycles[1] : 0,
    ];
    const rowItems = [[], []];
    originals.forEach((card, index) => rowItems[index % 2].push(card));

    const nextStage = document.createElement('div');
    nextStage.className = 'sponsor-marquee-stage';
    nextStage.tabIndex = 0;
    nextStage.setAttribute('aria-label', lang === 'zh'
      ? '赞助单位双行循环展示，支持拖动或横向滚轮控制'
      : 'Sponsor logos in two looping rows; drag or scroll horizontally to browse');

    const nextTracks = [0, 1].map(() => {
      const row = document.createElement('div');
      row.className = 'sponsor-marquee-row';
      const track = document.createElement('div');
      track.className = 'sponsor-marquee-track';
      row.append(track);
      nextStage.append(row);
      return track;
    });

    grid.classList.add('is-marquee');
    grid.replaceChildren(nextStage);

    const nextCycles = [
      populateTrack(nextTracks[0], rowItems[0], viewportWidth),
      populateTrack(nextTracks[1], rowItems[1], viewportWidth),
    ];
    if (nextCycles[0] <= 0 || nextCycles[1] <= 0) {
      mountStatic();
      return;
    }

    stage = nextStage;
    tracks = nextTracks;
    cycles = nextCycles;
    if (!staggered) {
      const avgCard = cycles[1] / Math.max(1, rowItems[1].length);
      offsets = [0, Math.round(avgCard * 0.55)];
      staggered = true;
    } else {
      offsets = [prevRatios[0] * cycles[0], prevRatios[1] * cycles[1]];
    }

    stage.addEventListener('pointerenter', e => { if (e.pointerType === 'mouse') hovered = true; });
    stage.addEventListener('pointerleave', e => { if (e.pointerType === 'mouse') hovered = false; });
    stage.addEventListener('focusin', () => { focusedWithin = true; });
    stage.addEventListener('focusout', e => { if (!stage.contains(e.relatedTarget)) focusedWithin = false; });

    stage.addEventListener('pointerdown', e => {
      if (e.pointerType === 'mouse' && e.button !== 0) return;
      dragging = true;
      activePointer = e.pointerId;
      startX = lastX = e.clientX;
      lastMoveTime = performance.now();
      dragMoved = false;
      velocity = 0;
      stage.classList.add('is-dragging');
    });

    stage.addEventListener('pointermove', e => {
      if (!dragging || e.pointerId !== activePointer) return;
      const now = performance.now();
      const dx = e.clientX - lastX;
      if (!dragMoved && Math.abs(e.clientX - startX) >= 5) {
        dragMoved = true;
        try { stage.setPointerCapture(e.pointerId); } catch {}
      }
      if (dragMoved) {
        offsets[0] -= dx;
        offsets[1] -= dx;
        const dt = Math.max(4, now - lastMoveTime) / 1000;
        const instant = -dx / dt;
        velocity = velocity * 0.65 + instant * 0.35;
        renderTracks();
      }
      lastX = e.clientX;
      lastMoveTime = now;
    });

    const endDrag = e => {
      if (!dragging || e.pointerId !== activePointer) return;
      dragging = false;
      activePointer = null;
      stage.classList.remove('is-dragging');
      try { if (stage.hasPointerCapture(e.pointerId)) stage.releasePointerCapture(e.pointerId); } catch {}
      if (dragMoved) {
        suppressClickUntil = performance.now() + 260;
        resumeAt = performance.now() + 900;
        velocity = Math.max(-1400, Math.min(1400, velocity));
      } else {
        velocity = 0;
      }
    };
    stage.addEventListener('pointerup', endDrag);
    stage.addEventListener('pointercancel', endDrag);

    stage.addEventListener('click', e => {
      if (performance.now() < suppressClickUntil) {
        e.preventDefault();
        e.stopPropagation();
      }
    }, true);

    stage.addEventListener('wheel', e => {
      const horizontal = Math.abs(e.deltaX) > 0 && Math.abs(e.deltaX) >= Math.abs(e.deltaY) * 0.5;
      const shiftWheel = e.shiftKey && e.deltaY !== 0;
      if (!horizontal && !shiftWheel) return;
      e.preventDefault();
      const scale = e.deltaMode === 1 ? 24 : 1;
      const stepDelta = (horizontal ? e.deltaX : e.deltaY) * scale;
      offsets[0] += stepDelta;
      offsets[1] += stepDelta;
      velocity = 0;
      resumeAt = performance.now() + 1200;
      renderTracks();
    }, {passive: false});

    stage.addEventListener('keydown', e => {
      if (e.key !== 'ArrowLeft' && e.key !== 'ArrowRight') return;
      e.preventDefault();
      const delta = e.key === 'ArrowRight' ? 180 : -180;
      offsets[0] += delta;
      offsets[1] += delta;
      velocity = 0;
      resumeAt = performance.now() + 1400;
      renderTracks();
    });

    isMarquee = true;
    renderTracks();
    startLoop();
  }

  function updateLayout(force = false) {
    const viewportWidth = grid.clientWidth;
    if (!viewportWidth) return;
    if (!force && Math.abs(viewportWidth - lastWidth) < 2) return;
    lastWidth = viewportWidth;
    const singleRowWidth = measureSingleRowWidth();
    if (singleRowWidth <= viewportWidth) {
      if (isMarquee) mountStatic();
    } else {
      mountMarquee(viewportWidth);
    }
  }

  new IntersectionObserver(([entry]) => {
    inViewport = entry.isIntersecting;
  }, {threshold: 0.01}).observe(grid);

  if (typeof ResizeObserver === 'function') {
    let timer = 0;
    new ResizeObserver(() => {
      window.clearTimeout(timer);
      timer = window.setTimeout(() => updateLayout(false), 80);
    }).observe(grid.parentElement || grid);
  }

  updateLayout(true);
  if (document.fonts && document.fonts.ready) {
    document.fonts.ready.then(() => updateLayout(true));
  }
}

for (const img of document.querySelectorAll('.author-avatar img')) {
  img.addEventListener('error', () => img.remove());
}
initSponsorMarquee();
loadStatus();
window.setInterval(loadStatus, 120000);
document.addEventListener('visibilitychange', loadStatus);
