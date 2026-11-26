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
    rankingsSummary: (people, proofs) => people + ' 位贡献者的 ' + proofs + ' 条引理已通过权威 Lean 验证。',
    rankingPeriods: { hour: '最近一小时', all_time: '累计' },
    justNow: '刚刚',
    participant: '参与者',
    activities: {
      claimed: '领取引理', submitted: '登记提交', checking: '开始验证',
      released: '归还引理', accepted: '验证通过', rejected: '验证拒绝', expired: '任务凭证过期'
    },
    event: '任务状态更新',
    verifiedCount: n => '通过 ' + n + ' 条',
    pullRequest: '查看 PR',
    allPrograms: '全部路线',
    programCount: (verified, published) => verified + ' / ' + published + ' 已通过',
    pageRange: (first, last, total) => '第 ' + first + '–' + last + ' 条，共 ' + total + ' 条',
    file: '证明文件',
    copyLemma: '复制这条引理的参与提示词',
    occupied: '这条引理当前正在处理。',
    alreadyVerified: '这条引理已通过权威验证。',
    lemmaPrompt: gap => '读取 ' + guideUrl + '，按指南用 ' + claimCommand + ' ' + gap.id + ' 领取并验证这一条引理。以领取结果的 gap.imports 为准。'
      + (gap.imports?.length ? '本题允许导入 ' + gap.imports.join('、') + '。' : '')
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
      proofs + (proofs === '1' ? ' proof accepted by Lean.' : ' proofs accepted by Lean.'),
    rankingPeriods: { hour: 'This hour', all_time: 'All time' },
    justNow: 'Just now',
    participant: 'Participant',
    activities: {
      claimed: 'Claimed a lemma', submitted: 'Registered a submission', checking: 'Started verification',
      released: 'Returned a lemma', accepted: 'Proof accepted', rejected: 'Proof rejected', expired: 'Lease expired'
    },
    event: 'Task status changed',
    verifiedCount: n => n === 1 ? '1 accepted' : n + ' accepted',
    pullRequest: 'View PR',
    allPrograms: 'All programs',
    programCount: (verified, published) => verified + ' / ' + published + ' verified',
    pageRange: (first, last, total) => first + '–' + last + ' of ' + total + ' lemmas',
    file: 'Proof file',
    copyLemma: 'Copy this lemma’s join prompt',
    occupied: 'This lemma is currently in progress.',
    alreadyVerified: 'The authoritative verifier has accepted this lemma.',
    lemmaPrompt: gap => 'Read ' + guideUrl + ' and follow it to claim and verify exactly ' + gap.id + ' with ' + claimCommand + ' ' + gap.id + '. Follow gap.imports from your claim. '
      + (gap.imports?.length ? 'Allowed imports for this task include ' + gap.imports.join(', ') + '. ' : '')
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
const rankingsAll = document.getElementById('rankings-all');
const rankingsDialog = document.getElementById('rankings-dialog');
const rankingsFullList = document.getElementById('rankings-full-list');
const rankingsAnnouncement = document.getElementById('rankings-announcement');
let rankingsData = null;
let rankingsSnapshot = null;
let rankingMode = null;
let agentRankingsData = null;
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
  if (gap.proved) return { label: strings.proved, kind: 'verified', style: 'accepted' };
  if (assigned(gap)) {
    return { label: strings.assignments[assignments[gap.id]], kind: 'occupied', style: 'in-progress' };
  }
  if (gap.claims_closed) return { label: closedClaimLabel(), kind: 'closed', style: '' };
  return { label: strings.open, kind: 'available', style: '' };
}

function canClaim(gap) {
  return !gap.claims_closed && !gap.refutation && !gap.proved && (!assigned(gap) || gap.parallel === true);
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
    detailContent.append(anchor(status.label + ' · PR #' + gap.refutation.pr, repository + '/pull/' + gap.refutation.pr, 'evidence-link'));
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

function renderLemmas() {
  const query = lemmaSearch.value.trim().toLocaleLowerCase();
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
      gap.id, gap.statement, gap.plain_statement.zh, gap.plain_statement.en,
      program, programName(program), gap.brief?.[lang] || ''
    ];
    return content.some(text => text.toLocaleLowerCase().includes(query));
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
  if (run.manifest) {
    const details = element('details', undefined, 'manifest');
    details.append(
      element('summary', strings.manifest),
      element('pre', JSON.stringify(run.manifest, null, 2))
    );
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
  const score = element('div', undefined, 'ranking-result');
  const figure = element('span', '+' + contributor.accepted.toLocaleString(locale), 'ranking-score');
  figure.setAttribute('aria-hidden', 'true');
  score.append(figure, element('span', strings.verifiedCount(contributor.accepted), 'sr-only'),
    element('span', strings.rankingPeriods[mode], 'ranking-period'));
  item.append(rank, avatar, identity, score);
  return item;
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

const agentBrandRules = [
  [/(?:^|[ /:_-])(?:codex)(?=$|[ /:_.0-9-])/, 22],
  [/(?:^|[ /:_-])(?:claude-code)(?=$|[ /:_.0-9-])/, 23],
  [/(?:^|[ /:_-])(?:gemini-cli)(?=$|[ /:_.0-9-])/, 25],
  [/(?:^|[ /:_-])(?:cursor)(?=$|[ /:_.0-9-])/, 24],
  [/(?:^|[ /:_-])(?:opencode)(?=$|[ /:_.0-9-])/, 26],
  [/(?:^|[ /:_-])(?:openai|gpt|chatgpt|o[134](?:-|$))(?=$|[ /:_.0-9-])/, 0],
  [/(?:^|[ /:_-])(?:anthropic|claude)(?=$|[ /:_.0-9-])/, 1],
  [/(?:^|[ /:_-])(?:gemini)(?=$|[ /:_.0-9-])/, 2],
  [/(?:^|[ /:_-])(?:deepseek)(?=$|[ /:_.0-9-])/, 3],
  [/(?:^|[ /:_-])(?:qwen|qwq|qvq|tongyi)(?=$|[ /:_.0-9-])/, 4],
  [/(?:^|[ /:_-])(?:xai|x-ai|grok)(?=$|[ /:_.0-9-])/, 5],
  [/(?:^|[ /:_-])(?:meta|llama)(?=$|[ /:_.0-9-])/, 6],
  [/(?:^|[ /:_-])(?:mistral|mixtral|codestral|devstral|magistral)(?=$|[ /:_.0-9-])/, 7],
  [/(?:^|[ /:_-])(?:kimi)(?=$|[ /:_.0-9-])/, 8],
  [/(?:^|[ /:_-])(?:moonshot)(?=$|[ /:_.0-9-])/, 33],
  [/(?:^|[ /:_-])(?:zhipu|zai|z-ai|glm|chatglm)(?=$|[ /:_.0-9-])/, 9],
  [/(?:^|[ /:_-])(?:doubao|seed|bytedance)(?=$|[ /:_.0-9-])/, 10],
  [/(?:^|[ /:_-])(?:baidu|ernie)(?=$|[ /:_.0-9-])/, 11],
  [/(?:^|[ /:_-])(?:minimax)(?=$|[ /:_.0-9-])/, 12],
  [/(?:^|[ /:_-])(?:yi(?:-|$)|01-ai)(?=$|[ /:_.0-9-])/, 13],
  [/(?:^|[ /:_-])(?:cohere|command)(?=$|[ /:_.0-9-])/, 14],
  [/(?:^|[ /:_-])(?:ai21|jamba)(?=$|[ /:_.0-9-])/, 15],
  [/(?:^|[ /:_-])(?:nvidia|nemotron)(?=$|[ /:_.0-9-])/, 16],
  [/(?:^|[ /:_-])(?:microsoft|phi)(?=$|[ /:_.0-9-])/, 17],
  [/(?:^|[ /:_-])(?:hunyuan)(?=$|[ /:_.0-9-])/, 18],
  [/(?:^|[ /:_-])(?:stepfun|step(?:-|$))(?=$|[ /:_.0-9-])/, 19],
  [/(?:^|[ /:_-])(?:gemma)(?=$|[ /:_.0-9-])/, 20],
  [/(?:^|[ /:_-])(?:google|palm)(?=$|[ /:_.0-9-])/, 21],
  [/(?:^|[ /:_-])(?:perplexity|sonar)(?=$|[ /:_.0-9-])/, 27],
  [/(?:^|[ /:_-])(?:alibaba)(?=$|[ /:_.0-9-])/, 28],
  [/(?:^|[ /:_-])(?:tencent)(?=$|[ /:_.0-9-])/, 29],
  [/(?:^|[ /:_-])(?:ibm|granite)(?=$|[ /:_.0-9-])/, 30],
  [/(?:^|[ /:_-])(?:huggingface|smollm)(?=$|[ /:_.0-9-])/, 31],
];

function agentBrandIcon(name) {
  const match = agentBrandRules.find(([pattern]) => pattern.test(name.toLowerCase()));
  const icon = element('span', match ? '' : name.slice(0, 1).toUpperCase(), 'agent-brand-icon');
  icon.setAttribute('aria-hidden', 'true');
  if (match) {
    icon.classList.add('has-brand');
    icon.style.backgroundPosition = '-' + (match[1] * 32) + 'px 0';
  }
  return icon;
}

function renderAgentRankingRow(entry, index) {
  const item = element('li', undefined, 'ranking-row agent-ranking-row');
  const name = element('strong', undefined, 'ranking-name agent-brand-name');
  name.append(agentBrandIcon(entry.name), element('span', agentName(entry.name)));
  item.append(element('span', index + 1, 'ranking-position'), name);
  const result = element('div', undefined, 'ranking-result');
  result.append(element('span', '+' + entry.accepted.toLocaleString(locale), 'ranking-score'),
    element('span', strings.rankingPeriods.all_time, 'ranking-period'));
  item.append(result);
  return item;
}

function renderAgentColumns(container, limit = Infinity) {
  container.replaceChildren(...['models', 'harnesses'].map(dimension => {
    const column = element('section', undefined, 'agent-ranking-column');
    const title = dimension === 'models' ? (lang === 'zh' ? '模型' : 'Models') : (lang === 'zh' ? 'Harness 工具' : 'Harness tools');
    const list = element('ol', undefined, 'ranking-list');
    list.setAttribute('aria-label', title);
    fillRankings(list, (agentRankingsData?.[dimension] || []).slice(0, limit), 'agents');
    column.append(element('h3', title), list);
    return column;
  }));
}

function renderFullRankings() {
  const agents = rankingMode === 'agents';
  const columns = document.getElementById('agent-rankings-full');
  columns.hidden = !agents;
  rankingsFullList.hidden = agents;
  if (agents) renderAgentColumns(columns);
  else fillRankings(rankingsFullList, rankingsData.all_time, 'all_time');
}

function fillRankings(list, data, mode) {
  const empty = mode === 'agents'
    ? (agentRankingsData ? (lang === 'zh' ? '暂无通过验证的记录。' : 'No verified contributions yet.') : strings.rankingsUnavailable)
    : mode === 'hour' ? strings.noHourContributors : strings.noContributors;
  list.replaceChildren(...(data.length
    ? data.map((entry, index) => mode === 'agents' ? renderAgentRankingRow(entry, index) : renderRankingRow(entry, index, mode))
    : [element('li', empty, 'ranking-empty')]));
}

function renderRankingMode() {
  if (!rankingsData) return;
  const agents = rankingMode === 'agents';
  const rows = agents ? (agentRankingsData?.models || []) : rankingsData[rankingMode];
  const columns = document.getElementById('agent-ranking-columns');
  columns.hidden = !agents;
  rankingsList.hidden = agents;
  if (agents) renderAgentColumns(columns, 6);
  document.getElementById('agent-ranking-controls').hidden = !agents;
  document.querySelector('.ranking-candidate').hidden = agents;
  rankingsAll.disabled = agents && !agentRankingsData;
  rankingsAll.textContent = agents ? (lang === 'zh' ? '查看完整榜单 ↗' : 'See full leaderboard ↗') :
    (lang === 'zh' ? '查看全部贡献者 ↗' : 'See all contributors ↗');
  document.getElementById('rankings-dialog-title').textContent = agents
    ? (lang === 'zh' ? '模型与 Harness 贡献榜' : 'Model and harness contributions')
    : (lang === 'zh' ? '全部已核验贡献者' : 'All verified contributors');
  document.getElementById('rankings-summary').textContent = agents
    ? (lang === 'zh' ? '按本研究台累计首次通过的引理数排列。' : 'Ranked by all-time first accepted lemmas on this research desk.')
    : strings.rankingsSummary(rankingsData.contributors.toLocaleString(locale), rankingsData.proofs.toLocaleString(locale));
  fillRankings(rankingsList, rows.slice(0, 6), rankingMode);
  document.getElementById('ranking-next-place').textContent = String(rows.length + 1);
  rankingsAnnouncement.textContent = agents ? (lang === 'zh' ? '共 ' + rows.length + ' 项。' : rows.length + ' entries.') : strings.rankingsCount(rows.length);
  if (rankingsDialog.open) renderFullRankings();
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
  rankingsAll.disabled = false;
  document.getElementById('rankings-summary').textContent = strings.rankingsSummary(
    rankings.contributors.toLocaleString(locale), rankings.proofs.toLocaleString(locale)
  );
  selectRankingMode(rankingMode ?? (rankings.hour.length ? 'hour' : 'all_time'));

}

for (const button of rankingsModes) {
  button.addEventListener('click', () => selectRankingMode(button.dataset.rankingMode));
}
rankingsAll.addEventListener('click', () => {
  renderFullRankings();
  rankingsDialog.showModal();
});

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

const activityPageSize = 6;
const activityPages = document.getElementById('activity-pages');
const activityPrev = document.getElementById('activity-prev');
const activityNext = document.getElementById('activity-next');
const activityPageLabel = document.getElementById('activity-page');
let activityItems = [];
let activityPage = 0;

function renderActivityPage() {
  const totalPages = Math.max(1, Math.ceil(activityItems.length / activityPageSize));
  if (activityPage >= totalPages) activityPage = totalPages - 1;
  const start = activityPage * activityPageSize;
  const slice = activityItems.slice(start, start + activityPageSize);
  deskActivity.replaceChildren(...(slice.length
    ? slice.map(renderActivity) : [element('li', strings.noActivity, 'empty-state')]));
  if (activityPages) {
    activityPages.hidden = activityItems.length <= activityPageSize;
    activityPrev.disabled = activityPage === 0;
    activityNext.disabled = activityPage >= totalPages - 1;
    activityPageLabel.textContent = lang === 'zh'
      ? '第 ' + (activityPage + 1) + ' / ' + totalPages + ' 页'
      : 'Page ' + (activityPage + 1) + ' / ' + totalPages;
  }
}

if (activityPrev && activityNext) {
  activityPrev.addEventListener('click', () => {
    if (activityPage > 0) {
      activityPage -= 1;
      renderActivityPage();
    }
  });
  activityNext.addEventListener('click', () => {
    if ((activityPage + 1) * activityPageSize < activityItems.length) {
      activityPage += 1;
      renderActivityPage();
    }
  });
}

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

// Each cursor identifies a boundary in this desk's immutable (run, attempt) order.
// The API returns 12 records per cursor batch; display 6 per UI page to keep the card compact.
const recordPageSize = 6;
const recordStarts = [''];
const recordPrev = document.getElementById('record-prev');
const recordNext = document.getElementById('record-next');
const recordRetry = document.getElementById('record-retry');
const recordPage = document.getElementById('record-page');
let recordBatchIndex = -1;
let recordBatchResults = [];
let recordSubPage = 0;
let currentRecordPage = 0;
let nextRecordCursor = null;
let recordPending = false;
let recordVisible = false;
let retryBatch = 0;
let retrySub = 0;
let latestRecordKey = '';
let displayedHead = null;

function syncRecordControls() {
  if (recordBatchIndex < 0) {
    recordPrev.disabled = true;
    recordNext.disabled = true;
    return;
  }
  const hasNextInBatch = (recordSubPage + 1) * recordPageSize < recordBatchResults.length;
  recordPrev.disabled = recordBatchIndex === 0 && recordSubPage === 0;
  recordNext.disabled = !(hasNextInBatch || nextRecordCursor);
}

function showRecordSlice(sub) {
  const maxSub = Math.max(0, Math.ceil(recordBatchResults.length / recordPageSize) - 1);
  recordSubPage = sub < 0 ? maxSub : Math.min(sub, maxSub);
  currentRecordPage = recordBatchIndex * 2 + recordSubPage;
  recordRetry.hidden = true;
  const start = recordSubPage * recordPageSize;
  renderResults(recordBatchResults.slice(start, start + recordPageSize));
  recordPage.textContent = lang === 'zh'
    ? '第 ' + (currentRecordPage + 1) + ' 页'
    : 'Page ' + (currentRecordPage + 1);
  syncRecordControls();
}

async function loadRecordPage(batchIndex, targetSub = 0) {
  if (recordPending) return;
  const cursor = recordStarts[batchIndex];
  const requestedHead = latestRecordKey;
  recordPending = true;
  recordPrev.disabled = recordNext.disabled = true;
  recordRetry.hidden = true;
  try {
    const response = await fetch('api/records' + (cursor ? '?before=' + encodeURIComponent(cursor) : ''),
      {signal: AbortSignal.timeout(15000)});
    if (!response.ok) throw new Error('Records unavailable');
    const page = await response.json();
    recordBatchIndex = batchIndex;
    recordBatchResults = Array.isArray(page.results) ? page.results : [];
    recordStarts.length = batchIndex + 1;
    nextRecordCursor = page.next;
    if (!batchIndex && targetSub === 0) displayedHead = requestedHead;
    showRecordSlice(targetSub);
  } catch {
    retryBatch = batchIndex;
    retrySub = targetSub;
    recordRetry.hidden = false;
    recordPage.textContent = strings.failure;
  } finally {
    recordPending = false;
    syncRecordControls();
  }
}

recordPrev.addEventListener('click', () => {
  if (recordPending || recordBatchIndex < 0) return;
  if (recordSubPage > 0) {
    showRecordSlice(recordSubPage - 1);
  } else if (recordBatchIndex > 0) {
    loadRecordPage(recordBatchIndex - 1, -1);
  }
});
recordNext.addEventListener('click', () => {
  if (recordPending || recordBatchIndex < 0) return;
  if ((recordSubPage + 1) * recordPageSize < recordBatchResults.length) {
    showRecordSlice(recordSubPage + 1);
  } else if (nextRecordCursor) {
    recordStarts[recordBatchIndex + 1] = nextRecordCursor;
    loadRecordPage(recordBatchIndex + 1, 0);
  }
});
recordRetry.addEventListener('click', () => loadRecordPage(retryBatch, retrySub));
new IntersectionObserver(([entry]) => {
  recordVisible = entry.isIntersecting;
  if (recordVisible && !currentRecordPage && displayedHead !== latestRecordKey) loadRecordPage(0, 0);
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
function status(g){if(g.refutation)return 'progress';if(g.proved)return 'verified';if(assigned(g))return 'progress';if(g.claims_closed)return 'closed';return g.role==='target'?'target':'available'}
function statusText(g){if(status(g)==='closed')return closedClaimLabel();if(g.refutation){const v=g.refutation.status==='verified';return lang==='zh'?(v?'已证伪':'反证待核验'):(v?'Refuted':'Refutation under review')}return ({verified:lang==='zh'?'已核查':'Verified',progress:lang==='zh'?'处理中':'In progress',target:lang==='zh'?'待突破':'Open target',available:lang==='zh'?'可领取':'Available'})[status(g)]}
function stateOK(g,v){return v==='all'||(v==='open'&&status(g)!=='verified')||(v==='target'&&g.role==='target'&&status(g)!=='verified')}
function counts(gs){let verified=gs.filter(g=>status(g)==='verified').length;return {verified,progress:gs.filter(g=>status(g)==='progress').length,available:gs.filter(g=>status(g)==='available').length,target:gs.filter(g=>status(g)==='target').length,pct:gs.length?100*verified/gs.length:0}}
function program(t){let c={};for(const g of groups.get(t.id))c[g.program]=(c[g.program]||0)+1;return Object.keys(c).sort((a,b)=>c[b]-c[a])[0]||'foundation'}
function trackSets(id){return {up:closure(id,x=>upstream.get(x)||[]),down:closure(id,x=>T.get(x)?.feeds||[])}}
function scrollRestore(){requestAnimationFrame(()=>{window.scrollTo({top:savedScrollY,behavior:'instant'});requestAnimationFrame(drawBoard)})}
function enterTrack(id,gap){if(!groups.has(id))return;if(!currentTrack)savedScrollY=window.scrollY;pendingGap=gap||null;if(location.hash===`#route=${encodeURIComponent(id)}`){renderRoute();return}location.hash=`route=${encodeURIComponent(id)}`}
function goOverview(){if(currentTrack)location.hash='';else renderRoute()}
function renderRoute(){let wasTrack=currentTrack;let m=location.hash.match(/^#route=(.+)$/),id=m?decodeURIComponent(m[1]):null;if(id&&!groups.has(id))id=null;currentTrack=id;observer?.disconnect();if(id){localFilter='all';localSearch='';indexMode=false;expanded=pendingGap;pendingGap=null;root.querySelector('#map-overview').hidden=true;root.querySelector('#map-route-view').hidden=false;root.querySelector('#map-focusbar').hidden=true;renderTrack();root.scrollIntoView({block:'start',behavior:'instant'});if(expanded)requestAnimationFrame(()=>root.querySelector(`[data-item="${CSS.escape(expanded)}"]`)?.scrollIntoView({block:'center'}));}else{root.querySelector('#map-overview').hidden=false;root.querySelector('#map-route-view').hidden=true;root.querySelector('#map-route-view').innerHTML='';renderBoard();renderFocus();if(wasTrack)scrollRestore()}}
function renderBoard(){let html='';let active=focus||hover,sets=active?trackSets(active):null,board=root.querySelector('#rm-board'),isHorizontal=horizontal&&window.innerWidth>640;board.classList.toggle('horizontal',isHorizontal);board.classList.toggle('chain-horizontal',isHorizontal&&onlyChain&&!!focus);for(let d=0;d<=Math.max(...distance.values());d++){let list=tracks.filter(t=>dist(t.id)===d).filter(t=>!onlyChain||!focus||sets.up.has(t.id)||sets.down.has(t.id)).filter(t=>groups.get(t.id).some(g=>(!field||(topic?programOf(g)===field:g.program===field))&&stateOK(g,globalFilter))).sort((a,b)=>Number(b.id.startsWith('frontier-'))-Number(a.id.startsWith('frontier-'))||a.title[lang].localeCompare(b.title[lang],locale));if(!list.length)continue;html+=`<section class="level" data-depth="${d}"><h3>${lang==='zh'?'第 '+(d+1)+' 层':'Layer '+(d+1)} · ${d===0?tr('直接汇合','Direct convergence'):`${tr('依赖深度','Dependency depth')} ${d}`}</h3><div class="grid count-${Math.min(list.length,4)}">`;for(const t of list){let gs=groups.get(t.id),c=counts(gs),n=gs.filter(g=>g.role==='target'&&status(g)!=='verified').length,muted=active&&!sets.up.has(t.id)&&!sets.down.has(t.id);html+=`<div class="track ${compact?'compact':'full'} ${focus===t.id?'selected':''} ${muted?'dim':''}" data-track="${esc(t.id)}" style="--c:${palette[program(t)]}" tabindex="0" role="button" aria-label="${tr('聚焦','Focus')} ${esc(t.title[lang])}" title="${esc(t.description[lang])}"><div class="track-title"><strong>${esc(t.title[lang])}</strong>${n?`<span class="target-badge">${lang==='zh'?`${n} 待突破`:`${n} open target${n===1?'':'s'}`}</span>`:''}</div>${compact?'':`<span class="description">${esc(t.description[lang])}</span>`}<span class="stats">${tr('已核查 / 全部','Verified / Total')}：${c.verified} / ${gs.length}</span><span class="bar"><i style="width:${c.pct}%"></i></span><button class="enter-small" data-enter="${esc(t.id)}">${tr('查看','View')} ${gs.length} ${tr('条引理','lemmas')} →</button></div>`}html+='</div></section>'}root.querySelector('#rm-levels').innerHTML=html;requestAnimationFrame(drawBoard)}
function drawBoard(){if(currentTrack)return;let board=root.querySelector('#rm-board'),svg=root.querySelector('#rm-board-svg');if(!board||!svg)return;let rect=board.getBoundingClientRect();svg.setAttribute('viewBox',`0 0 ${rect.width} ${rect.height}`);let active=focus||hover,sets=active?trackSets(active):null,isHorizontal=board.classList.contains('horizontal'),center=el=>{let r=el.getBoundingClientRect();return{x:r.left-rect.left+r.width/2,y:r.top-rect.top+r.height/2,left:r.left-rect.left,right:r.right-rect.left,top:r.top-rect.top,bottom:r.bottom-rect.top}},nodes=new Map([...board.querySelectorAll('[data-track]')].map(x=>[x.dataset.track,center(x)])),goal=center(root.querySelector('#rm-goal')),paths='';function edge(a,b,gold,op,from,to){let d;if(isHorizontal){let x1=a.right,x2=b.left-2,span=Math.max(0,x2-x1),lead=Math.min(12,Math.max(6,span*.22)),ex=x2-lead,dx=Math.max(8,(ex-x1)*.5);d=`M ${x1} ${a.y} C ${x1+dx} ${a.y}, ${ex-dx} ${b.y}, ${ex} ${b.y} L ${x2} ${b.y}`}else{let y1=a.top,y2=b.bottom+2,span=Math.max(0,y1-y2),lead=Math.min(12,Math.max(6,span*.22)),ey=y2+lead,dy=Math.max(10,(y1-ey)*.5);d=`M ${a.x} ${y1} C ${a.x} ${y1-dy}, ${b.x} ${ey+dy}, ${b.x} ${ey} L ${b.x} ${y2}`}paths+=`<path data-from="${esc(from)}" data-to="${esc(to)}" d="${d}" stroke="${gold?'#e3c580':'#a0c6a1'}" stroke-width="${active?2:0.85}" stroke-opacity="${op}" fill="none" marker-end="url(#arr-${gold?'gold':'mint'})"/>`}
for(const t of tracks){if(!nodes.has(t.id))continue;for(const f of t.feeds||[]){if(!nodes.has(f))continue;let down=active&&sets.down.has(t.id)&&sets.down.has(f),up=active&&sets.up.has(t.id)&&sets.up.has(f);if(!active||down||up)edge(nodes.get(t.id),nodes.get(f),!!down,active?.95:.2,t.id,f)}if(!(t.feeds||[]).length&&(!active||sets.down.has(t.id)))edge(nodes.get(t.id),goal,!!active,active?.95:.2,t.id,'goal')}
for(const el of board.querySelectorAll('[data-track]')){el.classList.toggle('selected',focus===el.dataset.track);el.classList.toggle('dim',!!active&&!sets.up.has(el.dataset.track)&&!sets.down.has(el.dataset.track))}svg.innerHTML=`<defs><marker id="arr-gold" viewBox="0 0 8 8" refX="8" refY="4" markerWidth="5.5" markerHeight="5.5" orient="auto"><path d="M0 0L8 4L0 8Z" fill="#e3c580"/></marker><marker id="arr-mint" viewBox="0 0 8 8" refX="8" refY="4" markerWidth="5.5" markerHeight="5.5" orient="auto"><path d="M0 0L8 4L0 8Z" fill="#a0c6a1"/></marker></defs>${paths}`}
function setFocus(id){let rebuild=onlyChain;focus=id;hover=null;if(!id)onlyChain=false;if(rebuild)renderBoard();else drawBoard();renderFocus()}
function renderFocus(){let bar=root.querySelector('#map-focusbar');bar.hidden=!focus||!!currentTrack;if(bar.hidden)return;let t=T.get(focus),up=upstream.get(focus)||[],down=t.feeds||[],buttons=a=>a.map(x=>`<button class="flow-focus" data-focus="${esc(x)}">${esc(T.get(x).title[lang])}</button>`).join('、'),summarize=a=>a.length>3?`${buttons(a.slice(0,3))} ${lang==='zh'?'等 '+a.length+' 条':'and '+a.length+' total'}`:buttons(a);bar.innerHTML=`<div class="focus-inner"><div class="focus-copy"><div class="flowline">${up.length?`${summarize(up)} → `:''}<b>${lang==='zh'?`【当前：${esc(t.title[lang])}】`:`Current: ${esc(t.title[lang])}`}</b>${down.length?` → ${summarize(down)}`:''} → ${esc(goalTitle())}</div></div><div class="focus-actions"><button id="chain-toggle" aria-pressed="${onlyChain}">${onlyChain?tr('显示全部路线','Show all routes'):tr('仅看相关链路','Related routes only')}</button><button data-enter="${esc(focus)}" class="primary">${tr('查看','View')} ${groups.get(focus).length} ${tr('条引理','lemmas')} →</button><button id="clear-focus">${tr('取消聚焦','Clear focus')}</button></div></div>`}
function gapGraph(id){let all=groups.get(id),set=new Set(all.map(g=>g.id)),parents=new Map(all.map(g=>[g.id,[]])),depths=new Map();for(const g of all)for(const d of g.depends_on||[])if(set.has(d))parents.get(d).push(g.id);function depth(g,seen=new Set()){if(depths.has(g.id))return depths.get(g.id);if(seen.has(g.id))return 0;let ns=new Set(seen);ns.add(g.id);let ds=(g.depends_on||[]).filter(x=>set.has(x)).map(x=>depth(G.get(x),ns));let n=ds.length?1+Math.max(...ds):0;depths.set(g.id,n);return n}all.forEach(g=>depth(g));return {set,parents,depths,hasEdges:all.some(g=>(g.depends_on||[]).some(x=>set.has(x)))}}
function gapRelated(id,graph){if(!id)return new Set();let a=closure(id,x=>(G.get(x)?.depends_on||[]).filter(d=>graph.set.has(d))),b=closure(id,x=>graph.parents.get(x)||[]);return new Set([...a,...b])}
function ordered(id,graph){let rank=g=>g.role==='target'?2:g.role==='conditional'?1:0;return [...groups.get(id)].sort((a,b)=>rank(b)-rank(a)||graph.depths.get(b.id)-graph.depths.get(a.id)||a.id.localeCompare(b.id,undefined,{numeric:true}))}
function details(g){let parents=gaps.filter(x=>(x.depends_on||[]).includes(g.id)),links=ids=>ids.length?ids.map(id=>`<button data-gap-jump="${esc(id)}">${esc(id)}</button>`).join(' · '):tr('无','None');return `<div class="detail-inline"><div class="detail-title"><b>${esc(g.id)}</b><span class="state ${status(g)}">● ${statusText(g)}</span><span class="role">${esc(roleName[g.role]||tr('命题','Statement'))}</span></div><p>${esc(g.plain_statement?.[lang]||tr('无中文说明','No statement available'))}</p>${g.brief?.[lang]?`<p class="muted">${esc(g.brief[lang])}</p>`:''}<div class="related"><b>${tr('上游依赖：','Prerequisites: ')}</b>${links(g.depends_on||[])}<br><b>${tr('下游影响：','Supports: ')}</b>${links(parents.map(x=>x.id))}</div><p class="muted">${tr('文件路径：','File: ')}${esc(g.file||tr('未指定','Not specified'))}</p><b>${tr('Lean 表述','Lean statement')}</b>${g.latest?runLink(g.latest,strings.latestRun).outerHTML:''}${g.refutation?` <a href="${repository}/pull/${Number(g.refutation.pr)}">${statusText(g)} · PR #${Number(g.refutation.pr)}</a>`:''}${g.source && /^https?:\/\//i.test(g.source)?` <a href="${esc(g.source)}" rel="noopener noreferrer">${tr('阅读来源 ↗','Read source ↗')}</a>`:''}<pre>${esc(g.statement||tr('未提供','Not provided'))}</pre></div>`}
function renderTrack(){if(!currentTrack)return;observer?.disconnect();let id=currentTrack,t=T.get(id),all=groups.get(id),graph=gapGraph(id),ct=counts(all),q=localSearch.trim().toLowerCase(),related=gapRelated(expanded,graph),shown=ordered(id,graph).filter(g=>stateOK(g,localFilter==='chain'?'all':localFilter)&&(!q||`${g.id} ${g.plain_statement?.[lang]||''} ${g.brief?.[lang]||''}`.toLowerCase().includes(q))&&(localFilter!=='chain'||related.has(g.id))),toButton=(x)=>`<button data-nav="${esc(x)}">${esc(T.get(x).title[lang])}</button>`,feed=t?.feeds||[],ups=upstream.get(id)||[];
let toolbar=[['all',`${tr('全部','All')} ${all.length}`],['open',tr('仅未通过','Not verified')],['target',tr('仅待突破','Open targets')],...(graph.hasEdges?[['chain',tr('仅依赖链','Dependency chain')]]:[])].map(([k,v])=>`<button data-filter="${k}" class="${localFilter===k?'active':''}">${v}</button>`).join('');
let rows=shown.map(g=>`<div class="item status-${status(g)}" data-item="${esc(g.id)}"><div class="row ${expanded===g.id?'active':''}" data-row="${esc(g.id)}" role="button" tabindex="0" aria-expanded="${expanded===g.id}"><span class="lemma-id" title="${esc(g.id)}">${esc(g.id.replace(/^L-goldbach-/,''))}</span><span class="state ${status(g)}">● ${statusText(g)}</span><span class="role">${esc(roleName[g.role]||tr('命题','Statement'))}</span><span class="statement">${esc(g.plain_statement?.[lang]||g.brief?.[lang]||tr('无中文说明','No statement available'))}</span><span class="expand">${expanded===g.id?tr('收起 ▴','Collapse ▴'):tr('展开 ▾','Expand ▾')}</span></div>${expanded===g.id?details(g):''}</div>`).join('');
let chips=shown.map(g=>`<button data-index="${esc(g.id)}" class="index-chip ${status(g)} ${expanded===g.id?'selected':''}" title="${esc(g.id)}"><span>●</span> ${esc(g.id.replace(/^L-goldbach-/,''))}</button>`).join('');
root.querySelector('#map-route-view').innerHTML=`<div class="backbar"><button id="back-overview">← ${tr('返回研究地图','Back to research map')}</button><span class="breadcrumb">${esc(goalTitle())} / ${t?`${lang==='zh'?'第 '+(dist(id)+1)+' 层':'Layer '+(dist(id)+1)} / ${esc(t.title[lang])}`:(id==='__goal'?tr('主命题','Main statement'):tr('核心主干引理','Core lemmas'))}</span></div><div class="track-header"><div class="header-info"><h1>${esc(t?.title[lang]||(id==='__goal'?tr('强哥德巴赫猜想','Strong Goldbach conjecture'):tr('核心主干引理','Core lemmas')))} <small>（${all.length} ${tr('条','lemmas')}）</small></h1><p>${esc(t?.description[lang]||(id==='__goal'?tr('查看主命题的正式表述。','Read the formal statement.'):tr('支撑研究地图的早期核心命题。','Early statements supporting the research map.')))}</p><div class="track-flows">${ups.length?`<span>${tr('上游路线：','Upstream: ')}</span>${ups.map(toButton).join(' ')}`:''}${feed.length?`<span>${tr('流向：','Feeds into: ')}</span>${feed.map(toButton).join(' ')}`:(t?`<span>${tr('流向：','Feeds into: ')}${esc(goalTitle())} →</span>`:'')}</div></div><div class="header-progress"><span>${tr('已核查 / 全部','Verified / Total')}</span><b>${ct.verified} / ${all.length}</b><div class="bar"><i style="width:${ct.pct}%"></i></div><div class="legend"><span class="verified">● ${tr('已核查','Verified')} ${ct.verified}</span><span class="target">● ${tr('待突破','Open targets')} ${ct.target}</span><span class="available">● ${tr('未通过','Not verified')} ${ct.progress+ct.available}</span></div></div></div><section class="track-content"><div class="toolbar">${toolbar}<input id="track-search" type="search" placeholder="${tr('路线内搜索编号或中文命题','Search ID or statement')}" value="${esc(localSearch)}"><div class="segments"><button data-view="list" class="${!indexMode?'active':''}">${tr('列表','List')}</button><button data-view="index" ${graph.hasEdges?`disabled title="${tr('该路线包含依赖关系','This route has dependencies')}"`:''} class="${indexMode?'active':''}">${tr('紧凑索引','Compact index')}</button></div></div><div class="countline">${tr('共','Total')} ${all.length} · ${tr('当前显示','shown')} ${shown.length}</div>${shown.length?(indexMode&&!graph.hasEdges?`<div class="index-area">${expanded&&shown.some(g=>g.id===expanded)?`<div class="index-detail" data-item="${esc(expanded)}">${details(G.get(expanded))}</div>`:''}<div class="index-grid">${chips}</div></div>`:`<div class="proof ${graph.hasEdges?'has-rail':''}">${graph.hasEdges?`<div class="rail"><svg aria-label="${tr('路线内真实依赖关系','Dependencies within this route')}"></svg></div>`:''}<div class="listing"><div class="table-head"><span>${tr('引理编号','Lemma ID')}</span><span>${tr('状态','Status')}</span><span>${tr('角色','Role')}</span><span>${tr('引理陈述','Statement')}</span><span>${tr('操作','Action')}</span></div><div class="items">${rows}</div></div></div>`):`<p class="empty">${tr('没有匹配的命题；请选择全部或清除搜索。','No matches; clear the search or filters.')}</p>`}</section>`;
if(graph.hasEdges&&shown.length&&!indexMode){let container=root.querySelector('.items');observer=new ResizeObserver(()=>drawRail(id));observer.observe(container);for(const item of container.children)observer.observe(item);requestAnimationFrame(()=>drawRail(id))}}
function drawRail(id){if(id!==currentTrack)return;let rail=root.querySelector('.rail'),svg=rail?.querySelector('svg'),container=root.querySelector('.items');if(!svg||!container)return;let graph=gapGraph(id),items=[...container.querySelectorAll('.item')],map=new Map(items.map((it,i)=>{let row=it.querySelector('.row').getBoundingClientRect(),base=rail.getBoundingClientRect();return [it.dataset.item,{y:row.top+row.height/2-base.top,index:i}]})),w=rail.clientWidth,h=container.offsetHeight+(container.getBoundingClientRect().top-rail.getBoundingClientRect().top),orderedAll=ordered(id,graph),assigned=new Map(),xFor=i=>12+(w-28)*i/4;for(const [i,g] of orderedAll.entries()){let ps=graph.parents.get(g.id)||[],parent=ps.find(x=>assigned.has(x)),siblings=parent?(G.get(parent).depends_on||[]).filter(x=>graph.set.has(x)):[],j=siblings.indexOf(g.id);assigned.set(g.id,g.role==='target'||g.role==='endpoint'?4:parent&&j===0?assigned.get(parent):(graph.depths.get(g.id)+Math.max(0,j)+i)%4)}for(const [id,n] of map)n.x=xFor(assigned.get(id));let rel=gapRelated(expanded,graph),paths='';for(const [key,n] of map)for(const dep of G.get(key).depends_on||[])if(map.has(dep)){let a=map.get(dep),b=n,mid=(a.y+b.y)/2,on=rel.has(key)&&rel.has(dep);paths+=`<path data-from="${esc(dep)}" data-to="${esc(key)}" d="M${a.x} ${a.y} L${a.x} ${mid} C${a.x} ${mid-10},${b.x} ${mid+10},${b.x} ${mid} L${b.x} ${b.y}" stroke="${on?'#e3c580':'#a4b9a5'}" stroke-opacity="${expanded&&!on?.2:.75}" stroke-width="${on?2:1}" fill="none"/>`}
for(const [key,n] of map){let target=G.get(key).role==='target';if(key===expanded)paths+=`<path d="M${n.x} ${n.y}H${w}" stroke="#e3c580" stroke-width="1.5"/>`;if(target)paths+=`<circle cx="${n.x}" cy="${n.y}" r="8" fill="#183126" stroke="#e3c580"/><path d="M${n.x} ${n.y-9}v-8 m-3 3 3-3 3 3" fill="none" stroke="#e3c580"/>`;paths+=`<circle data-node="${esc(key)}" cx="${n.x}" cy="${n.y}" r="${target?5:3.5}" fill="${rel.has(key)||target?'#e3c580':'#d8e5d8'}"/>`}rail.style.height=h+'px';svg.style.height=h+'px';svg.setAttribute('viewBox',`0 0 ${w} ${h}`);svg.innerHTML=paths}
function expandGap(id){expanded=expanded===id?null:id;let old=window.scrollY;renderTrack();window.scrollTo({top:old,behavior:'instant'})}
function jumpGap(id){let g=G.get(id);if(!g)return;let tid=groupOf(g);if(currentTrack!==tid){enterTrack(tid,id);return}localFilter='all';localSearch='';expanded=id;renderTrack();requestAnimationFrame(()=>root.querySelector(`[data-item="${CSS.escape(id)}"]`)?.scrollIntoView({block:'center',behavior:'smooth'}))}
root.addEventListener('click',e=>{let el=e.target.closest('button,[data-track],[data-row],[data-goal]');if(!el){if(e.target.closest('#rm-board')&&focus)setFocus(null);return}if(el.dataset.goal&&!topic){enterTrack('__goal',endpointId);return}if(el.dataset.direction){horizontal=el.dataset.direction==='horizontal';directionChosen=true;try{localStorage.setItem(directionKey,el.dataset.direction)}catch{}syncDirection();renderBoard();return}if(el.dataset.cards){compact=el.dataset.cards==='compact';root.querySelectorAll('[data-cards]').forEach(x=>x.classList.toggle('active',x===el));renderBoard();return}if(el.dataset.focus){setFocus(el.dataset.focus);return}if(el.id==='clear-focus'){setFocus(null);return}if(el.id==='chain-toggle'){onlyChain=!onlyChain;renderBoard();renderFocus();return}if(el.id==='back-overview'){goOverview();return}if(el.dataset.enter){enterTrack(el.dataset.enter);return}if(el.dataset.nav){enterTrack(el.dataset.nav);return}if(el.dataset.gapJump){jumpGap(el.dataset.gapJump);return}if(el.dataset.resultGap){enterTrack(groupOf(G.get(el.dataset.resultGap)),el.dataset.resultGap);return}if(el.dataset.resultTrack){enterTrack(el.dataset.resultTrack);return}if(el.dataset.program)return;if(el.dataset.filter){localFilter=el.dataset.filter;if(localFilter==='chain'&&!expanded){let g=ordered(currentTrack,gapGraph(currentTrack)).find(g=>g.role==='target')||groups.get(currentTrack)[0];expanded=g.id}renderTrack();return}if(el.dataset.view){indexMode=el.dataset.view==='index';renderTrack();return}if(el.dataset.index){expandGap(el.dataset.index);return}if(el.dataset.row){expandGap(el.dataset.row);return}if(el.dataset.track){setFocus(el.dataset.track);return}});
root.addEventListener('dblclick',e=>{let el=e.target.closest('[data-track]');if(el&&!e.target.closest('button'))enterTrack(el.dataset.track)});root.addEventListener('keydown',e=>{if((e.key==='Enter'||e.key===' ')&&e.target.matches('[data-track],[data-row],[data-goal]')){e.preventDefault();e.target.click()}});
root.addEventListener('pointerover',e=>{let card=e.target.closest('[data-track]');if(card&&!focus&&hover!==card.dataset.track){hover=card.dataset.track;drawBoard()}});root.addEventListener('pointerout',e=>{let card=e.target.closest('[data-track]');if(card&&!focus&&!card.contains(e.relatedTarget)){hover=null;drawBoard()}});
root.querySelector('#rm-state').addEventListener('change',e=>{globalFilter=e.target.value;renderBoard()});root.addEventListener('input',e=>{if(e.target.id==='track-search'){let val=e.target.value,pos=e.target.selectionStart;localSearch=val;renderTrack();let input=root.querySelector('#track-search');input.focus();input.setSelectionRange(pos,pos)}if(e.target.id==='rm-search'){let q=e.target.value.trim().toLowerCase(),box=root.querySelector('#rm-search-results');if(!q){box.innerHTML='';return}let ts=tracks.filter(t=>`${t.id} ${t.title[lang]}`.toLowerCase().includes(q)),gs=gaps.filter(g=>`${g.id} ${g.plain_statement?.[lang]||''}`.toLowerCase().includes(q));box.innerHTML=`<span>${ts.length} ${tr('条路线','routes')} · ${gs.length} ${tr('条命题匹配','matching lemmas')}:</span>`+ts.map(t=>`<button data-result-track="${esc(t.id)}">${esc(t.title[lang])}</button>`).join(' ')+gs.map(g=>`<button data-result-gap="${esc(g.id)}">${esc(g.id)}</button>`).join(' ')}});
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
    const incremental = lastGaps !== null && Boolean(cachedRevision);
    const response = await fetch(incremental ? 'api/status?view=board-delta-gzip' : 'api/status?view=board-gzip', {
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
    const delta = incremental ? new Map(data.gaps.map(gap => [gap.id, gap])) : null;
    const gaps = delta ? publishedGaps.map(gap => ({ ...gap, ...delta.get(gap.id) })) : data.gaps;
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
      ? latest.lemma_id + ' · ' + (latest.verdict === 'ACCEPTED' ? strings.accepted : strings.rejected)
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
    if (recordVisible && !currentRecordPage && displayedHead !== latestRecordKey) loadRecordPage(0);
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

loadStatus();
window.setInterval(loadStatus, 120000);
document.addEventListener('visibilitychange', loadStatus);
