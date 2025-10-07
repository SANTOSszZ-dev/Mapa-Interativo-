/* script.js
  Expectativa de formato:

  data/stations.json -> [
    {"id":"se","name":"Sé","coords":[-23.5502,-46.6333],"lines":["linha-1-azul","linha-3-vermelha"]},
    ...
  ]

  data/lines.json -> [
    {"id":"linha-1-azul","name":"Linha 1 - Azul","color":"#0056d6","stations":["jabaquara","conceicao", ...]},
    ...
  ]
*/

const MAP_BOUNDS = [[-23.9, -46.95], [-23.15, -46.2]]; // limites aproximados SP
const DEFAULT_CENTER = [-23.5505, -46.6333];

let map = L.map('map', {
  center: DEFAULT_CENTER,
  zoom: 12,
  maxBounds: MAP_BOUNDS,
  maxBoundsViscosity: 1.0
});
L.tileLayer('https://{s}.tile.openstreetmap.org/{z}/{x}/{y}.png', { maxZoom: 19 }).addTo(map);

/* Marker clustering for performance */
const markersCluster = L.markerClusterGroup({ chunkedLoading: true });
map.addLayer(markersCluster);

/* UI elements */
const originSelect = document.getElementById('originSelect');
const destSelect = document.getElementById('destSelect');
const calcRouteBtn = document.getElementById('calcRouteBtn');
const clearRouteBtn = document.getElementById('clearRouteBtn');
const progressArea = document.getElementById('progressArea');
const linesListDiv = document.getElementById('linesList');
const searchBox = document.getElementById('searchBox');
const searchBtn = document.getElementById('searchBtn');

/* Data holders */
let stations = {};    // id => station {id,name,coords,lines}
let lines = [];       // array of line objects {id,name,color,stations: [id...]}

let stationMarkers = {}; // id => marker
let drawnLineLayers = []; // polylines for clearing
let routeLayer = null;


const SAMPLE_LINES = [
  {id:"linha-1-azul", name:"Linha 1 - Azul", color:"#0056d6", stations:["jabaquara","se","luz","tucuruvi"]},
  {id:"linha-3-vermelha", name:"Linha 3 - Vermelha", color:"#e50000", stations:["se"]},
  {id:"linha-7-rubi", name:"Linha 7 - Rubi", color:"#b02a24", stations:["luz"]},
  {id:"linha-11-coral", name:"Linha 11 - Coral", color:"#ff7f00", stations:["luz"]},
  {id:"linha-4-amarela", name:"Linha 4 - Amarela", color:"#ffd400", stations:["luz"]}
];

/* Utility: load JSON with fallback */
async function tryLoadJSON(path, fallback){
  try{
    const r = await fetch(path);
    if(!r.ok) throw new Error('not found');
    return await r.json();
  } catch(e){
    console.warn('Fallback for', path, e);
    return fallback;
  }
}

/* Haversine distance (meters) */
function haversine(a, b){
  const toRad = v => v * Math.PI / 180;
  const [lat1, lon1] = a;
  const [lat2, lon2] = b;
  const R = 6371000;
  const dLat = toRad(lat2 - lat1);
  const dLon = toRad(lon2 - lon1);
  const A = Math.sin(dLat/2)*Math.sin(dLat/2) + Math.cos(toRad(lat1))*Math.cos(toRad(lat2))*Math.sin(dLon/2)*Math.sin(dLon/2);
  const C = 2 * Math.atan2(Math.sqrt(A), Math.sqrt(1-A));
  return R * C;
}

/* Build graph from lines: adjacency list with weights */
function buildGraph(lines, stationsMap){
  const graph = {}; // id => [{to, weight, lineId}]
  function ensure(n){ if(!graph[n]) graph[n]=[]; }
  lines.forEach(line=>{
    const seq = line.stations;
    for(let i=0;i<seq.length-1;i++){
      const a = seq[i], b = seq[i+1];
      const sa = stationsMap[a], sb = stationsMap[b];
      if(!sa || !sb || !sa.coords || !sb.coords) continue;
      const dist = haversine(sa.coords, sb.coords);
      ensure(a); ensure(b);
      // undirected
      graph[a].push({to:b, weight:dist, lineId:line.id});
      graph[b].push({to:a, weight:dist, lineId:line.id});
    }
  });
  return graph;
}

/* Dijkstra (returns path of station ids) */
function dijkstra(graph, start, target){
  const dist = {};
  const prev = {};
  const visited = new Set();
  const pq = new MinPriorityQueue(); // custom small PQ below

  Object.keys(graph).forEach(n => { dist[n] = Infinity; prev[n] = null; });
  dist[start] = 0;
  pq.push(start, 0);

  while(!pq.isEmpty()){
    const u = pq.pop();
    if(visited.has(u)) continue;
    visited.add(u);
    if(u === target) break;
    (graph[u] || []).forEach(edge =>{
      const v = edge.to;
      const alt = dist[u] + edge.weight;
      if(alt < (dist[v] || Infinity)){
        dist[v] = alt;
        prev[v] = u;
        pq.push(v, alt);
      }
    });
  }

  // reconstruct path
  if(!prev[target] && start !== target) return null;
  const path = [];
  let u = target;
  while(u){
    path.unshift(u);
    u = prev[u];
  }
  return path;
}

/* Minimal binary heap priority queue (for Dijkstra) */
class MinPriorityQueue {
  constructor(){ this._heap=[]; }
  push(value, priority){
    this._heap.push({value, priority});
    this._siftUp();
  }
  pop(){
    if(this._heap.length===0) return null;
    const root = this._heap[0].value;
    const last = this._heap.pop();
    if(this._heap.length>0){
      this._heap[0] = last;
      this._siftDown();
    }
    return root;
  }
  isEmpty(){ return this._heap.length===0; }
  _siftUp(){
    let idx = this._heap.length-1;
    while(idx>0){
      const p = Math.floor((idx-1)/2);
      if(this._heap[p].priority <= this._heap[idx].priority) break;
      [this._heap[p], this._heap[idx]] = [this._heap[idx], this._heap[p]];
      idx = p;
    }
  }
  _siftDown(){
    let idx = 0, len = this._heap.length;
    while(true){
      const left = 2*idx+1, right = 2*idx+2;
      let smallest = idx;
      if(left < len && this._heap[left].priority < this._heap[smallest].priority) smallest = left;
      if(right < len && this._heap[right].priority < this._heap[smallest].priority) smallest = right;
      if(smallest === idx) break;
      [this._heap[smallest], this._heap[idx]] = [this._heap[idx], this._heap[smallest]];
      idx = smallest;
    }
  }
}

/* Populate selects and sidebar, draw everything */
async function init(){
  progressArea.innerHTML = 'Carregando dados (stations.json / lines.json)...';
  const rawStations = await tryLoadJSON('data/stations.json', SAMPLE_STATIONS);
  const rawLines = await tryLoadJSON('data/lines.json', SAMPLE_LINES);

  // Normalize stations map
  stations = {};
  rawStations.forEach(s => {
    // expect coords [lat,lng]
    stations[s.id] = {
      id: s.id,
      name: s.name || s.id,
      coords: s.coords || null,
      lines: s.lines || []
    };
  });

  // Normalize lines
  lines = rawLines.map(l => ({...l}));

  progressArea.innerHTML = `Estacões carregadas: ${Object.keys(stations).length}. Linhas: ${lines.length}. Desenhando...`;

  // draw lines polylines and prepare lines list in sidebar
  drawnLineLayers.forEach(l => map.removeLayer(l));
  drawnLineLayers = [];
  linesListDiv.innerHTML = '';
  lines.forEach(line=>{
    // build coords array from station ids
    const coords = line.stations.map(id => stations[id] && stations[id].coords).filter(Boolean);
    if(coords.length >= 2){
      const poly = L.polyline(coords, {color: line.color, weight: 5, opacity:0.9}).addTo(map);
      drawnLineLayers.push(poly);
    }
    const badge = document.createElement('div');
    badge.className = 'line-badge';
    badge.style.background = line.color;
    badge.textContent = line.name;
    badge.title = line.name;
    badge.onclick = ()=>{ // zoom to line
      if(coords.length) map.fitBounds(coords, {padding:[30,30]});
    };
    linesListDiv.appendChild(badge);
  });

  // add station markers
  markersCluster.clearLayers();
  stationMarkers = {};
  Object.values(stations).forEach(s=>{
    if(!s.coords) return;
    const marker = L.marker(s.coords, {title:s.name});
    const popupHtml = `<strong>${s.name}</strong><br/><small>${(s.lines||[]).join(', ')}</small>`;
    marker.bindPopup(popupHtml);
    markersCluster.addLayer(marker);
    stationMarkers[s.id] = marker;
  });

  // fill origin/dest selects (sorted by name)
  const stationList = Object.values(stations).filter(s=>s.coords).sort((a,b)=>a.name.localeCompare(b.name));
  originSelect.innerHTML = '<option value="">Selecione origem...</option>';
  destSelect.innerHTML = '<option value="">Selecione destino...</option>';
  stationList.forEach(s=>{
    const o1 = document.createElement('option'); o1.value = s.id; o1.textContent = s.name;
    const o2 = document.createElement('option'); o2.value = s.id; o2.textContent = s.name;
    originSelect.appendChild(o1); destSelect.appendChild(o2);
  });

  progressArea.innerHTML = 'Mapa desenhado. Pronto para calcular rotas.';

  // build graph for routing
  const graph = buildGraph(lines, stations);

  // event: calculate route
  calcRouteBtn.onclick = ()=> {
    const origin = originSelect.value;
    const dest = destSelect.value;
    if(!origin || !dest){ alert('Selecione origem e destino.'); return; }
    if(!graph[origin] || !graph[dest]){ alert('Origem ou destino não estão conectados à malha carregada.'); return; }

    const path = dijkstra(graph, origin, dest);
    if(!path){ alert('Nenhuma rota encontrada.'); return; }
    renderRoute(path);
    renderRouteSteps(path);
  };

  clearRouteBtn.onclick = ()=>{
    if(routeLayer) map.removeLayer(routeLayer);
    routeLayer = null;
    document.getElementById('routeInfo').innerHTML = '';
  };

  // search
  searchBtn.onclick = ()=>{
    const q = searchBox.value.trim().toLowerCase();
    if(!q) return;
    const found = Object.values(stations).find(s => s.name.toLowerCase().includes(q));
    if(found && found.coords){
      map.setView(found.coords, 15);
      if(stationMarkers[found.id]) stationMarkers[found.id].openPopup();
    } else {
      alert('Estação não encontrada localmente.');
    }
  };

  document.getElementById('focusSP').onclick = ()=> map.setView(DEFAULT_CENTER, 12);
}

/* Render route polyline from path (array of station ids) */
function renderRoute(path){
  if(routeLayer) map.removeLayer(routeLayer);
  const coords = path.map(id => stations[id].coords).filter(Boolean);
  routeLayer = L.polyline(coords, {color:'#7b2cbf', weight:6, opacity:0.95}).addTo(map);
  map.fitBounds(routeLayer.getBounds(), {padding:[40,40]});
}

/* Render route steps: show station list with possible transfers */
function renderRouteSteps(path){
  const routeInfo = document.getElementById('routeInfo');
  routeInfo.innerHTML = '';
  if(!path || path.length===0) { routeInfo.textContent = 'Rota vazia'; return; }

  // compute lines used between consecutive stations to detect transfers
  const segments = [];
  for(let i=0;i<path.length-1;i++){
    const a = stations[path[i]], b = stations[path[i+1]];
    // find common line between a and b
    const common = (a.lines || []).filter(x => (b.lines || []).includes(x));
    const usedLine = common.length ? common[0] : null;
    segments.push({from:a, to:b, line:usedLine});
  }

  // compress segments by same line
  const steps = [];
  let cur = null;
  segments.forEach(seg=>{
    if(!cur){
      cur = {line: seg.line, stations: [seg.from.name, seg.to.name]};
    } else {
      if(seg.line === cur.line){
        cur.stations.push(seg.to.name);
      } else {
        steps.push(cur);
        cur = {line: seg.line, stations: [seg.from.name, seg.to.name]};
      }
    }
  });
  if(cur) steps.push(cur);

  // display
  const ul = document.createElement('ol');
  steps.forEach(step=>{
    const li = document.createElement('li');
    const lineName = step.line ? (lines.find(l=>l.id===step.line)?.name || step.line) : 'Linha desconhecida';
    li.innerHTML = `<strong>${lineName}</strong>: ${step.stations[0]} → ${step.stations[step.stations.length-1]} (${step.stations.length} estações)`;
    ul.appendChild(li);
  });
  routeInfo.appendChild(ul);
}

/* Graph builder reused from previous implementation */
function buildGraph(lines, stationsMap){
  const graph = {};
  const ensure = n => { if(!graph[n]) graph[n]=[]; };
  lines.forEach(line=>{
    for(let i=0;i<line.stations.length-1;i++){
      const a = line.stations[i], b = line.stations[i+1];
      const sa = stationsMap[a], sb = stationsMap[b];
      if(!sa || !sb || !sa.coords || !sb.coords) continue;
      const dist = haversine(sa.coords, sb.coords);
      ensure(a); ensure(b);
      graph[a].push({to:b, weight:dist, lineId:line.id});
      graph[b].push({to:a, weight:dist, lineId:line.id});
    }
  });
  return graph;
}

/* minimal helper functions reused (haversine & dijkstra classes already above) */
function haversine(a,b){
  const toRad = v => v * Math.PI / 180;
  const [lat1, lon1] = a;
  const [lat2, lon2] = b;
  const R = 6371000;
  const dLat = toRad(lat2 - lat1);
  const dLon = toRad(lon2 - lon1);
  const A = Math.sin(dLat/2)*Math.sin(dLat/2) + Math.cos(toRad(lat1))*Math.cos(toRad(lat2))*Math.sin(dLon/2)*Math.sin(dLon/2);
  const C = 2 * Math.atan2(Math.sqrt(A), Math.sqrt(1-A));
  return R * C;
}

/* run init */
init().catch(e=>{ console.error(e); progressArea.innerHTML = 'Erro ao inicializar: '+e.message; });

// Lista de estações da Linha 11-Coral com coordenadas aproximadas
const estacoes = [
  { nome: "Luz", coords: [-23.5343, -46.6345] },
  { nome: "Brás", coords: [-23.54521834862633, -46.61611052813644] },
  { nome: "Tatuapé", coords: [-23.54022376294034, -46.57640274733506] },
  { nome: "Corinthians-Itaquera", coords: [-23.5424, -46.4718] },
  { nome: "Dom Bosco", coords: [-23.54180631364945, -46.448143324603144] },
  { nome: "José Bonifácio", coords: [-23.539064851664353, -46.431699699301355] },
  { nome: "Guaianases", coords: [-23.54227047133191, -46.415620733841095] },
  { nome: "Antônio Gianetti Neto", coords: [-23.554390613726426, -46.383614189663895] },
  { nome: "Ferraz de Vasconcelos", coords: [-23.540699970980636, -46.368283562676496] },
  { nome: "Poá", coords: [-23.52543444901898, -46.34359481637673] },
  { nome: "Calmon Viana", coords: [-23.5253878046452, -46.333255205006324] },
  { nome: "Suzano", coords: [-23.534156746739416, -46.30795280579012] },
  { nome: "Jundiapeba", coords: [-23.542781007234083, -46.258104891511884] },
  { nome: "Brás Cubas", coords: [-23.536310469998863, -46.22518073384136] },
  { nome: "Mogi das Cruzes", coords: [-23.5224, -46.1924] },
  { nome: "Estudantes", coords: [-23.5215, -46.1771] }
];



// Camada base
L.tileLayer("https://{s}.tile.openstreetmap.org/{z}/{x}/{y}.png", {
  attribution: "© OpenStreetMap contributors"
}).addTo(map);

// Marcadores e linha
let coordsLinha = [];

estacoes.forEach(estacao => {
  L.marker(estacao.coords)
    .addTo(map)
    .bindPopup(`<b>${estacao.nome}</b><br>Linha 11-Coral`);
  coordsLinha.push(estacao.coords);
});

// Desenha a linha da CPTM
L.polyline(coordsLinha, { color: "coral", weight: 5 }).addTo(map);
