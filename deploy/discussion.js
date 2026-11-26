const heroItems = Array.from(document.querySelectorAll('.hero-community details.community-item'));
const coreTeam = document.querySelector('#core-team');
const desktopHero = window.matchMedia('(min-width: 726px)');

function syncHeroCommunity() {
  if (!heroItems.length) return;
  for (const item of heroItems) {
    if (desktopHero.matches) {
      item.removeAttribute('name');
      item.open = true;
    } else {
      item.setAttribute('name', 'hero-community-qr');
      item.open = location.hash === '#core-team' && item === coreTeam;
    }
  }
}

function followCoreTeamLink() {
  if (coreTeam && location.hash === '#core-team') {
    coreTeam.open = true;
    coreTeam.scrollIntoView({ block: 'center' });
  }
}

syncHeroCommunity();
desktopHero.addEventListener('change', syncHeroCommunity);
followCoreTeamLink();
window.addEventListener('hashchange', followCoreTeamLink);
