// The manuscript's main mathematical dependencies, not a Lean import graph.
const results = {
  association: {
    title: 'Capped association', kind: 'Lemma 2 · an association inequality', step: 2,
    statement: 'For the capped uniform load law μ, two symmetric statistics that increase as loads become more concentrated have nonnegative covariance.',
    formula: 'Cov<sub>μ</sub>(F, G) ≥ 0',
    foundation: 'The written proof specializes Cohen–Sackrowitz’s association theorem to the truncated factorial carrier 1/k!. This ingredient does not use the two-bin lemma.',
    context: 'The capped-load visualization shows how association turns a change of density into an expectation comparison. Lean proves the required finite rational association statement directly.'
  },
  pair: {
    title: 'Two-bin coefficients', kind: 'Lemma 3 · one calculation, two uses', step: 1,
    statement: 'If every choice row prefers the first of two bins, the normalized coefficients of their product are nondecreasing and discretely convex. Both properties hold even when some factors vanish.',
    formula: 'Δg<sub>k</sub> ≥ 0 &nbsp; and &nbsp; Δ²g<sub>k</sub> ≥ 0',
    foundation: 'Average products over permutations. Taking a first or second difference replaces one or two factors v with u − v. All remaining factors are nonnegative.',
    context: 'The first differences feed the next-choice lemma; the second differences feed the concentration theorem. The slider illustrates both on the same coefficient sequence.'
  },
  concentration: {
    title: 'Conditional concentration', kind: 'Theorem 4 · comparing capped load laws', step: 2,
    statement: 'For independent choices whose rows share one order, condition on all loads staying at most q. Every symmetric, concentration-increasing statistic has expectation at least as large as under capped uniform choices.',
    formula: 'E<sub>ordered</sub>F ≥ E<sub>μ</sub>F',
    context: 'After symmetrizing bin labels, write the conditioned law with normalized density L relative to μ. The comparison is Covμ(F, L) ≥ 0. Conditioning must have positive probability.'
  },
  next: {
    title: 'The uniform next choice minimizes the hazard', kind: 'Lemma 5 · ordering boundary probabilities', step: 3,
    statement: 'Under the cap event, bins earlier in the shared order are at least as likely to be at load q. An independent next choice with the same preference order therefore hits that boundary at least as often as a uniform choice.',
    formula: 'Σ v<sub>i</sub>p<sub>i</sub> ≥ (Σ p<sub>i</sub>) / b',
    context: 'Here pᵢ is the conditional probability that bin i is at load q. This is the first inequality in the saturation visualization; keep the old distribution fixed and vary the next-choice preference.'
  },
  hazard: {
    title: 'The conditional hazard bound', kind: 'Corollary 6 · where the two branches meet', step: 3,
    statement: 'For capacity C = q + 1, commonly ordered old choices and an independent ordered next choice create a full bin with probability at least the uniform reference h. All rows uniform give equality.',
    formula: 'Pr(N<sub>Y</sub> = C − 1 | max N < C) ≥ h<sub>b,C</sub>(r)',
    context: 'Two comparisons are needed: first make the next choice uniform; then compare the old loads with the capped uniform reference. This covers every positive integer capacity, on a positive-probability cap event.'
  },
  transition: {
    title: 'The actual conditional transition', kind: 'Lemma 7 · bringing the bound into the algorithms', step: 4,
    statement: 'At a fixed accepted-job count K, condition on the current arrival index and the number a of full bins. Both algorithms have the stated next-success waiting law. Given the next success, the probability of adding a full bin equals h for RV and is at least h for RANKING.',
    formula: 'RV fill probability = h ≤ RANKING fill probability',
    context: 'The additional work is identifying the conditional law: refine the history, factor its weight, and show the residual cap is its entire remaining constraint. Averaging over refinements preserves the hazard bound. The visualization illustrates this history argument.'
  },
  coupling: {
    title: 'Coupling the acceptance levels', kind: 'Section 4 · proof argument', step: 5,
    statement: 'At every acceptance level, couple the actual state distributions so that RV reaches that level no later and has no more full bins whenever RANKING reaches it. Use a shared waiting quantile, and compare fill increments when old full-bin counts agree.',
    formula: 'σ<sub>K,RV</sub> ≤ σ<sub>K,RK</sub>; &nbsp; A<sub>K,RV</sub> ≤ A<sub>K,RK</sub>',
    context: 'The count inequality applies when RANKING reaches K. Never-reached levels use an absorbing state. Induction and total probability preserve the correct one-time marginals; no Markov assumption is needed.'
  },
  main: {
    title: 'Matching-size stochastic dominance', kind: 'Theorem 1 · the conclusion', step: 6,
    statement: 'With equal positive capacities and independent uniform feasible sets of prescribed sizes, RV accepts at least K jobs with probability no smaller than RANKING, for every K. Independent random arrival and priority orders are included by averaging.',
    formula: 'Pr(M<sub>RV</sub> ≥ K) ≥ Pr(M<sub>RANKING</sub> ≥ K)',
    context: 'Reaching level K by the last arrival is exactly the event M ≥ K. Relabeling and averaging identify the source model; Theorem 8 states that formal version explicitly. The map groups these as one conclusion.'
  }
};

const edges = [
  {from: 'association', to: 'concentration', label: 'association',
    role: 'Nonnegative covariance converts the increasing density into an expectation comparison.'},
  {from: 'pair', to: 'concentration', label: 'convexity', diagonal: true,
    role: 'Convexity shows that balancing two loads cannot increase the symmetrized density L.'},
  {from: 'pair', to: 'next', label: 'monotonicity',
    role: 'Monotonicity compares the two boundary coefficients and orders the bin boundary probabilities.'},
  {from: 'concentration', to: 'hazard', label: 'old loads',
    role: 'Apply the concentration comparison to B(x), the number of bins at load q, to bound the uniform-next-choice hazard.'},
  {from: 'next', to: 'hazard', label: 'next choice',
    role: 'Replacing the ordered next choice with a uniform one cannot increase the probability of filling a bin.'},
  {from: 'hazard', to: 'transition', label: 'apply inside each history refinement',
    role: 'Once the residual history law is identified, apply the hazard bound inside each refinement and then average.'},
  {from: 'transition', to: 'coupling', label: 'waiting law + fill probability',
    role: 'The conditional waiting laws and fill probabilities supply the actual marginals for each coupled transition.'},
  {from: 'coupling', to: 'main', label: 'hitting times → matching tails',
    role: 'Ordered hitting times compare every matching-size tail; relabeling and averaging give the random-order source model.'}
];

export function initProofMap(explore) {
  const get = id => document.getElementById(id);
  const graph = get('proof-graph');
  const svg = get('proof-edges');
  const buttons = [...graph.querySelectorAll('[data-result]')];
  const nodes = Object.fromEntries(buttons.map(button => [button.dataset.result, button]));
  const initial = location.hash.match(/^#map-([a-z]+)$/)?.[1];
  let selected = Object.hasOwn(results, initial) ? initial : 'hazard';

  function drawEdges() {
    const bounds = graph.getBoundingClientRect();
    svg.setAttribute('viewBox', `0 0 ${bounds.width} ${bounds.height}`);
    const box = id => {
      const b = nodes[id].getBoundingClientRect();
      return {x: b.left - bounds.left, y: b.top - bounds.top, w: b.width, h: b.height};
    };
    let content = '<defs>';
    for (const state of ['idle', 'active']) {
      content += `<marker id="map-arrow-${state}" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto"><path d="M 1 1 L 9 5 L 1 9" fill="none" stroke="${state === 'active' ? '#176c60' : '#86968c'}" stroke-width="1.5"/></marker>`;
    }
    content += '</defs>';
    for (const edge of edges) {
      const from = box(edge.from), to = box(edge.to);
      const state = edge.to === selected ? 'active' : 'idle';
      let x1 = from.x + from.w / 2, x2 = to.x + to.w / 2;
      const y1 = from.y + from.h + 2, y2 = to.y - 5;
      if (edge.diagonal) { x1 = from.x + from.w * .12; x2 = to.x + to.w * .88; }
      if (edge.to === 'hazard') x2 = to.x + to.w * (edge.from === 'concentration' ? .2 : .8);
      const midY = (y1 + y2) / 2;
      const path = `M ${x1} ${y1} C ${x1} ${midY} ${x2} ${midY} ${x2} ${y2}`;
      const labelX = (x1 + x2) / 2, labelY = midY - 5;
      content += `<g class="proof-edge ${state}" data-from="${edge.from}" data-to="${edge.to}"><path d="${path}" marker-end="url(#map-arrow-${state})"/><text x="${labelX}" y="${labelY}" text-anchor="middle">${edge.label}</text></g>`;
    }
    svg.innerHTML = content;
  }

  function select(id, {announce = true, updateHash = true} = {}) {
    if (!Object.hasOwn(results, id)) return;
    selected = id;
    const result = results[id];
    const inputs = edges.filter(edge => edge.to === id);
    const outputs = edges.filter(edge => edge.from === id);
    const parents = new Set(inputs.map(edge => edge.from));
    for (const button of buttons) {
      button.setAttribute('aria-pressed', String(button.dataset.result === id));
      button.classList.toggle('is-prerequisite', parents.has(button.dataset.result));
    }
    get('map-kind').textContent = result.kind;
    get('map-title').textContent = result.title;
    get('map-statement').textContent = result.statement;
    get('map-formula').innerHTML = result.formula;
    get('map-inputs').innerHTML = inputs.length ? '<ul>' + inputs.map(edge =>
      `<li><button class="map-result-link" data-select="${edge.from}">${results[edge.from].title}</button><p>${edge.role}</p></li>`
    ).join('') + '</ul>' : `<p>${result.foundation}</p>`;
    get('map-outputs').innerHTML = outputs.length ? outputs.map(edge =>
      `<button class="map-result-link" data-select="${edge.to}">${results[edge.to].title} →</button>`
    ).join('') : '<p>This is the conclusion: the comparison holds for every matching-size threshold.</p>';
    get('map-context').textContent = result.context;
    get('map-explore').textContent = id === 'main' ? 'Explore the conclusion ↓' : 'Explore this result ↓';
    if (announce) get('map-announcement').textContent = `${result.title}. ${inputs.length ? 'Uses ' + inputs.map(edge => results[edge.from].title).join(' and ') + '.' : 'Starting ingredient; no incoming dependency on this map.'}`;
    if (updateHash) history.replaceState(null, '', '#map-' + id);
    drawEdges();
  }

  buttons.forEach(button => button.addEventListener('click', event => {
    select(button.dataset.result);
    // Bring the statement into view when the details are below the graph.
    if (event.detail > 0 && matchMedia('(max-width: 900px)').matches) {
      get('map-detail').scrollIntoView({block: 'start'});
      get('map-title').focus({preventScroll: true});
    }
  }));
  get('map-detail').addEventListener('click', event => {
    const button = event.target.closest('[data-select]');
    if (button) { select(button.dataset.select); get('map-title').focus({preventScroll: true}); }
  });
  get('map-explore').addEventListener('click', () => explore(results[selected].step));
  window.addEventListener('hashchange', () => {
    const id = location.hash.match(/^#map-([a-z]+)$/)?.[1];
    if (Object.hasOwn(results, id)) { select(id, {updateHash: false}); get('proof-map').scrollIntoView({block: 'start'}); }
  });
  new ResizeObserver(drawEdges).observe(graph);
  select(selected, {announce: false, updateHash: false});
  if (Object.hasOwn(results, initial)) requestAnimationFrame(() => get('proof-map').scrollIntoView({block: 'start'}));
}
