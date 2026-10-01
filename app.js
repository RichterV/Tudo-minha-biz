// Reorganiza os pixels de uma foto qualquer para formar "original.jpeg".
// Mesmo algoritmo do reorganizar.py, rodando no navegador:
//   1. a foto é recortada e redimensionada para o mesmo número de pixels do alvo;
//   2. pixels são pareados por luminosidade (CIELAB);
//   3. trocas de pares que diminuem o erro refinam o resultado;
//   4. cada pixel é animado da posição de origem até a posição final.

// Usa a imagem embutida (original-data.js) quando disponível: imagens data: não
// "contaminam" o canvas, então funciona até abrindo o index.html direto do disco.
const ALVO_URL = window.ALVO_DATA || "original.jpeg";
const LARGURA = 480;   // resolução de trabalho (pixels na horizontal)
const DURACAO = 12;    // segundos de animação

const $ = (s) => document.querySelector(s);
const tela = $("#tela");
const ctx = tela.getContext("2d");
const status = $("#status");
const progresso = $("#progresso");

let imagemAlvo = null;   // HTMLImageElement do alvo
let animacao = null;     // dados prontos para animar
let quadroId = 0;

// ---------- utilidades ----------

function carregarImagem(src) {
  return new Promise((ok, erro) => {
    const img = new Image();
    img.onload = () => ok(img);
    img.onerror = () => erro(new Error("não foi possível carregar " + src));
    img.src = src;
  });
}

const proximoQuadro = () => new Promise(requestAnimationFrame);

// Desenha a imagem preenchendo w×h (recorte central, como "object-fit: cover").
function pixelsCover(img, w, h) {
  const c = document.createElement("canvas");
  c.width = w;
  c.height = h;
  const g = c.getContext("2d");
  const iw = img.naturalWidth, ih = img.naturalHeight;
  const escala = Math.max(w / iw, h / ih);
  const sw = w / escala, sh = h / escala;
  g.imageSmoothingQuality = "high";
  g.drawImage(img, (iw - sw) / 2, (ih - sh) / 2, sw, sh, 0, 0, w, h);
  return g.getImageData(0, 0, w, h);
}

// sRGB (RGBA uint8) -> CIELAB D65, em um Float32Array [L,a,b, L,a,b, ...]
const LINEAR = new Float32Array(256).map((_, i) => {
  const c = i / 255;
  return c <= 0.04045 ? c / 12.92 : ((c + 0.055) / 1.055) ** 2.4;
});
function rgbaParaLab(rgba, n) {
  const lab = new Float32Array(n * 3);
  const d3 = (6 / 29) ** 3, k = 3 * (6 / 29) ** 2;
  const f = (t) => (t > d3 ? Math.cbrt(t) : t / k + 4 / 29);
  for (let i = 0; i < n; i++) {
    const r = LINEAR[rgba[i * 4]], g = LINEAR[rgba[i * 4 + 1]], b = LINEAR[rgba[i * 4 + 2]];
    const fx = f((0.4124 * r + 0.3576 * g + 0.1805 * b) / 0.95047);
    const fy = f(0.2126 * r + 0.7152 * g + 0.0722 * b);
    const fz = f((0.0193 * r + 0.1192 * g + 0.9505 * b) / 1.08883);
    lab[i * 3] = 116 * fy - 16;
    lab[i * 3 + 1] = 500 * (fx - fy);
    lab[i * 3 + 2] = 200 * (fy - fz);
  }
  return lab;
}

// Índices ordenados por chave. Empacota chave+índice num Float64 para usar o
// sort numérico nativo, bem mais rápido que sort com comparador.
const DESLOC = 2 ** 21;
function argsort(chaves) {
  const n = chaves.length;
  let min = Infinity, max = -Infinity;
  for (const v of chaves) { if (v < min) min = v; if (v > max) max = v; }
  const escala = 1e6 / (max - min || 1);
  const pacote = new Float64Array(n);
  for (let i = 0; i < n; i++) pacote[i] = Math.floor((chaves[i] - min) * escala) * DESLOC + i;
  pacote.sort();
  const idx = new Uint32Array(n);
  for (let i = 0; i < n; i++) idx[i] = pacote[i] % DESLOC;
  return idx;
}

function erroMedio(F, T, perm) {
  let soma = 0;
  for (let p = 0; p < perm.length; p++) {
    const s = perm[p] * 3, t = p * 3;
    soma += Math.hypot(F[s] - T[t], F[s + 1] - T[t + 1], F[s + 2] - T[t + 2]);
  }
  return soma / perm.length;
}

// ---------- algoritmo ----------

// Devolve perm, onde perm[posição no alvo] = índice do pixel da foto.
async function reorganizar(F, T, n, iteracoes, aoProgredir) {
  const L_F = new Float32Array(n), L_T = new Float32Array(n);
  for (let i = 0; i < n; i++) { L_F[i] = F[i * 3]; L_T[i] = T[i * 3]; }

  // 1) Atribuição inicial por luminosidade.
  const ordF = argsort(L_F), ordT = argsort(L_T);
  const perm = new Uint32Array(n);
  for (let i = 0; i < n; i++) perm[ordT[i]] = ordF[i];

  // 2) Trocas de pares. As posições são ordenadas por uma projeção aleatória
  //    da cor alvo, então vizinhas nessa ordem querem cores parecidas.
  const proj = new Float32Array(n);
  let ordem = null;
  for (let it = 0; it < iteracoes; it++) {
    if (it % 25 === 0) {
      const dx = (Math.random() * 2 - 1) * 2, dy = Math.random() * 2 - 1, dz = Math.random() * 2 - 1;
      for (let i = 0; i < n; i++) proj[i] = T[i * 3] * dx + T[i * 3 + 1] * dy + T[i * 3 + 2] * dz;
      ordem = argsort(proj);
    }
    // Distância log-uniforme entre parceiros: trocas locais e distantes.
    const d = Math.max(1, Math.floor(Math.exp(Math.random() * Math.log(n / 4))));
    const inicio = Math.floor(Math.random() * 2 * d);
    for (let bloco = inicio; bloco + d < n; bloco += 2 * d) {
      const fim = Math.min(bloco + d, n - d);
      for (let k = bloco; k < fim; k++) {
        const a = ordem[k], b = ordem[k + d];
        const ca = perm[a] * 3, cb = perm[b] * 3, ta = a * 3, tb = b * 3;
        // ganho da troca = 2·(Ca−Cb)·(Tb−Ta)
        const ganho =
          (F[ca] - F[cb]) * (T[tb] - T[ta]) +
          (F[ca + 1] - F[cb + 1]) * (T[tb + 1] - T[ta + 1]) +
          (F[ca + 2] - F[cb + 2]) * (T[tb + 2] - T[ta + 2]);
        if (ganho > 0) { const x = perm[a]; perm[a] = perm[b]; perm[b] = x; }
      }
    }
    if (it % 20 === 0) { aoProgredir(it / iteracoes); await proximoQuadro(); }
  }
  return perm;
}

// ---------- animação ----------

function prepararAnimacao(foto, perm, w, h) {
  const n = w * h;
  const cores = new Uint32Array(foto.data.buffer.slice(0));  // RGBA da foto, 1 uint32 por pixel
  const ox = new Float32Array(n), oy = new Float32Array(n);
  const dx = new Float32Array(n), dy = new Float32Array(n);
  const atraso = new Float32Array(n), curva = new Float32Array(n);
  for (let p = 0; p < n; p++) {
    const s = perm[p];               // o pixel s da foto vai para a posição p
    ox[s] = s % w; oy[s] = (s / w) | 0;
    dx[s] = p % w; dy[s] = (p / w) | 0;
    atraso[s] = Math.random() * 0.35;
    curva[s] = (Math.random() * 2 - 1) * 0.25;
  }
  return { w, h, n, cores, ox, oy, dx, dy, atraso, curva, saida: ctx.createImageData(w, h) };
}

const suavizar = (t) => (t < 0.5 ? 4 * t * t * t : 1 - (-2 * t + 2) ** 3 / 2);

function desenhar(anim, t) {
  const { w, h, n, cores, ox, oy, dx, dy, atraso, curva, saida } = anim;
  const px = new Uint32Array(saida.data.buffer);
  px.fill(0xff000000);
  const janela = 1 - 0.35;
  for (let s = 0; s < n; s++) {
    let p = (t - atraso[s]) / janela;
    p = p <= 0 ? 0 : p >= 1 ? 1 : suavizar(p);
    // trajetória levemente curva: desvio perpendicular que some nas pontas
    const vx = dx[s] - ox[s], vy = dy[s] - oy[s];
    const arco = Math.sin(Math.PI * p) * curva[s];
    let x = ox[s] + vx * p - vy * arco;
    let y = oy[s] + vy * p + vx * arco;
    x = x < 0 ? 0 : x > w - 1 ? w - 1 : x;
    y = y < 0 ? 0 : y > h - 1 ? h - 1 : y;
    px[((y + 0.5) | 0) * w + ((x + 0.5) | 0)] = cores[s];
  }
  ctx.putImageData(saida, 0, 0);
}

function tocar() {
  if (!animacao) return;
  cancelAnimationFrame(quadroId);
  const pausa = 800;  // mostra a foto parada antes de começar
  const duracao = DURACAO * 1000;
  const t0 = performance.now();
  const passo = (agora) => {
    const t = Math.min(1, Math.max(0, (agora - t0 - pausa) / duracao));
    desenhar(animacao, t);
    if (t < 1) quadroId = requestAnimationFrame(passo);
    else $("#outra").hidden = false;
  };
  quadroId = requestAnimationFrame(passo);
}

// ---------- fluxo principal ----------

async function processar(img) {
  cancelAnimationFrame(quadroId);
  $("#intro").hidden = true;
  $("#outra").hidden = true;

  imagemAlvo ??= await carregarImagem(ALVO_URL);
  const w = LARGURA;
  const h = Math.round((w * imagemAlvo.naturalHeight) / imagemAlvo.naturalWidth);
  const n = w * h;
  tela.width = w;
  tela.height = h;

  const alvo = pixelsCover(imagemAlvo, w, h);
  const foto = pixelsCover(img, w, h);
  ctx.putImageData(foto, 0, 0);

  status.textContent = "Consultando o universo sobre o destino de cada pixel…";
  progresso.hidden = false;
  await proximoQuadro();

  const F = rgbaParaLab(foto.data, n);
  const T = rgbaParaLab(alvo.data, n);
  const perm = await reorganizar(F, T, n, 600, (p) => (progresso.value = p));

  progresso.hidden = true;
  status.textContent =
    `Confirmado: ${n.toLocaleString("pt-BR")} pixels seus sempre foram minha biz. ` +
    `Margem de erro cósmico: ΔE ${erroMedio(F, T, perm).toFixed(1)}.`;

  animacao = prepararAnimacao(foto, perm, w, h);
  tocar();
}

async function aoEscolher(arquivo) {
  if (!arquivo || !arquivo.type.startsWith("image/")) return;
  try {
    const url = URL.createObjectURL(arquivo);
    const img = await carregarImagem(url);
    await processar(img);
    URL.revokeObjectURL(url);
  } catch (e) {
    status.textContent = "O universo engasgou: " + e.message;
    progresso.hidden = true;
  }
}

$("#arquivo").addEventListener("change", (e) => {
  aoEscolher(e.target.files[0]);
  e.target.value = "";  // permite escolher a mesma foto de novo
});

// arrastar e soltar
const palco = $(".palco");
palco.addEventListener("dragover", (e) => { e.preventDefault(); palco.classList.add("arrastando"); });
palco.addEventListener("dragleave", () => palco.classList.remove("arrastando"));
palco.addEventListener("drop", (e) => {
  e.preventDefault();
  palco.classList.remove("arrastando");
  aoEscolher(e.dataTransfer.files[0]);
});

// Quebra os textos .psico em palavras, cada uma com seu índice (--i), para a
// animação de entrada em sequência e a ondulação contínua defasada.
let indice = 0;
for (const el of document.querySelectorAll(".psico")) {
  const palavras = el.textContent.trim().split(/\s+/);
  el.textContent = "";
  palavras.forEach((p, k) => {
    const span = document.createElement("span");
    span.className = "palavra";
    span.textContent = p;
    span.style.setProperty("--i", indice++);
    el.append(span, k < palavras.length - 1 ? " " : "");
  });
  indice += 4;  // pausa entre o título e o parágrafo
}
// convite e botão entram depois do texto
$("#convite").style.setProperty("--i", indice);
$("#enviar").style.setProperty("--i", indice + 3);
