(() => {
  const widgets = Array.from(document.querySelectorAll('.presence-widget'));
  if (!widgets.length) return;
  const endpoint = new URL(widgets[0].dataset.endpoint, document.baseURI);
  const cookiePath = new URL('../', endpoint).pathname;
  const format = new Intl.NumberFormat(document.documentElement.lang);
  const fields = ['visitors', 'agents', 'page_views', 'unique_ips'];
  const slots = Object.fromEntries(
    fields.map(key => [key, widgets.flatMap(w => Array.from(w.querySelectorAll(`[data-count="${key}"]`)))])
  );
  let visit;
  let timer;
  let pending = false;

  function visitorId() {
    // A short-lived first-party ID lets tabs share a visit, even behind a shared IP.
    try {
      visit = /(?:^|;\s*)goldbach_visit=([0-9a-f]{32})(?:;|$)/.exec(document.cookie)?.[1] || visit;
    } catch {}
    visit ||= crypto.randomUUID().replaceAll('-', '');
    try {
      document.cookie = `goldbach_visit=${visit}; Path=${cookiePath}; Max-Age=120; SameSite=Strict; Secure`;
    } catch {}
    return visit;
  }

  function render(value) {
    for (const key of fields) {
      const text = value && Number.isSafeInteger(value[key]) ? format.format(value[key]) : '—';
      for (const node of slots[key]) node.textContent = text;
    }
  }

  async function refresh() {
    if (pending || document.hidden) return;
    pending = true;
    const controller = new AbortController();
    const timeout = setTimeout(() => controller.abort(), 8000);
    try {
      const response = await fetch(endpoint, {
        method: 'POST', headers: { 'X-Goldbach-Visit': visitorId() },
        cache: 'no-store', signal: controller.signal
      });
      if (!response.ok) throw new Error('Presence unavailable');
      render(await response.json());
    } catch {
      render(null);
    } finally {
      clearTimeout(timeout);
      pending = false;
    }
  }

  function watch() {
    clearInterval(timer);
    if (!document.hidden) {
      refresh();
      timer = setInterval(refresh, 30000);
    }
  }
  for (const widget of widgets) widget.hidden = false;
  document.addEventListener('visibilitychange', watch);
  window.addEventListener('pagehide', () => clearInterval(timer));
  window.addEventListener('pageshow', watch);
  watch();
})();
