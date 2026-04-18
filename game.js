const canvas = document.getElementById("maze");
const ctx = canvas.getContext("2d");
const statusEl = document.getElementById("status");
const scoreEl = document.getElementById("score");
const stepsEl = document.getElementById("steps");
const winPopupEl = document.getElementById("winPopup");
const winOverlayEl = document.getElementById("winOverlay");
const trollPopupEl = document.getElementById("trollPopup");
const trollOverlayEl = document.getElementById("trollOverlay");
const homeMenu = document.getElementById("homeMenu");
const welcomeOverlayEl = document.getElementById("welcomeOverlay");
const easyBtn = document.getElementById("easyBtn");
const hardBtn = document.getElementById("hardBtn");
const impossibleBtn = document.getElementById("impossibleBtn");
const newGameBtn = document.getElementById("newGameBtn");
const themeBtn = document.getElementById("themeBtn");
const themeModal = document.getElementById("themeModal");
const themeModalClose = document.querySelector(".theme-modal-close");
const themeModalOverlay = document.querySelector(".theme-modal-overlay");
const sizeSelect = document.getElementById("sizeSelect");
const themeBtns = document.querySelectorAll(".theme-btn");

let currentTheme = "arctic-ice";
let difficulty = "easy"; // "easy", "hard", or "impossible"
let stepCount = 0;
let optimalPathLength = 0;
let lastPlayerPosition = { x: 0, y: 0 };
let gridSize = Number(sizeSelect.value);
let cellSize = canvas.width / gridSize;
let maze = [];
let player = { x: 0, y: 0 };
let renderPlayer = { x: 0, y: 0 };
let exit = { x: gridSize - 1, y: gridSize - 1, variant: "square" };
let gameWon = false;
let isAnimatingMove = false;
const moveDurationMs = 135;
let trail = [];
const maxTrailPoints = 320;
const trailLifetimeMs = 2200;
const moveQueue = [];
const maxQueuedMoves = 3;
let fadeFrameId = null;
let touchStart = null;
const exitVariants = ["square", "circle", "diamond", "ring"];
let playerPoints = 0;
let pointOrbs = [];
let enemies = [];
const enemyRevealDistance = 7;
let isTrollLevel = false;
let scorePopups = [];
const popupDurationMs = 700;
let flyingCoins = [];
const coinFlightDurationMs = 900;
let audioContext = null;
let trollAmbientNodes = null;
let trollPulseIntervalId = null;
let trollPopupTimeoutId = null;
let trollIdlePopupTimeoutId = null;
let distancesFromStart = [];
let distanceToExit = Infinity;
let maxDistanceToExit = Infinity;
let playerMaxProgress = Infinity;
let gameStarted = false;

function makeCell() {
  return {
    visited: false,
    walls: {
      top: true,
      right: true,
      bottom: true,
      left: true,
    },
  };
}

function initMaze() {
  maze = Array.from({ length: gridSize }, () =>
    Array.from({ length: gridSize }, () => makeCell())
  );

  // Frontier-based generation creates a bushier maze with more short dead ends.
  const frontier = [];
  const frontierKeys = new Set();

  function pushFrontier(x, y) {
    if (x < 0 || x >= gridSize || y < 0 || y >= gridSize) return;
    const cellKey = keyFor(x, y);
    if (maze[y][x].visited || frontierKeys.has(cellKey)) return;
    frontier.push({ x, y });
    frontierKeys.add(cellKey);
  }

  function getVisitedNeighbors(x, y) {
    const neighbors = [];
    if (y > 0 && maze[y - 1][x].visited) neighbors.push({ x, y: y - 1 });
    if (x < gridSize - 1 && maze[y][x + 1].visited) neighbors.push({ x: x + 1, y });
    if (y < gridSize - 1 && maze[y + 1][x].visited) neighbors.push({ x, y: y + 1 });
    if (x > 0 && maze[y][x - 1].visited) neighbors.push({ x: x - 1, y });
    return neighbors;
  }

  maze[0][0].visited = true;
  pushFrontier(1, 0);
  pushFrontier(0, 1);

  while (frontier.length > 0) {
    const index = Math.floor(Math.random() * frontier.length);
    const cell = frontier.splice(index, 1)[0];
    frontierKeys.delete(keyFor(cell.x, cell.y));

    const neighbors = getVisitedNeighbors(cell.x, cell.y);
    if (neighbors.length === 0) continue;

    const connectTo = neighbors[Math.floor(Math.random() * neighbors.length)];
    removeWalls(cell, connectTo);
    maze[cell.y][cell.x].visited = true;

    pushFrontier(cell.x, cell.y - 1);
    pushFrontier(cell.x + 1, cell.y);
    pushFrontier(cell.x, cell.y + 1);
    pushFrontier(cell.x - 1, cell.y);
  }

  for (const row of maze) {
    for (const cell of row) {
      cell.visited = false;
    }
  }
}

function getUnvisitedNeighbors(x, y) {
  const dirs = [
    { dx: 0, dy: -1, dir: "top" },
    { dx: 1, dy: 0, dir: "right" },
    { dx: 0, dy: 1, dir: "bottom" },
    { dx: -1, dy: 0, dir: "left" },
  ];

  const result = [];
  for (const d of dirs) {
    const nx = x + d.dx;
    const ny = y + d.dy;

    if (nx >= 0 && nx < gridSize && ny >= 0 && ny < gridSize && !maze[ny][nx].visited) {
      result.push({ x: nx, y: ny, from: d.dir });
    }
  }
  return result;
}

function removeWalls(a, b) {
  const dx = b.x - a.x;
  const dy = b.y - a.y;

  if (dx === 1) {
    maze[a.y][a.x].walls.right = false;
    maze[b.y][b.x].walls.left = false;
  } else if (dx === -1) {
    maze[a.y][a.x].walls.left = false;
    maze[b.y][b.x].walls.right = false;
  } else if (dy === 1) {
    maze[a.y][a.x].walls.bottom = false;
    maze[b.y][b.x].walls.top = false;
  } else if (dy === -1) {
    maze[a.y][a.x].walls.top = false;
    maze[b.y][b.x].walls.bottom = false;
  }
}

function drawMaze() {
  ctx.clearRect(0, 0, canvas.width, canvas.height);
  ctx.fillStyle = getCssVar("--path");
  ctx.fillRect(0, 0, canvas.width, canvas.height);

  ctx.strokeStyle = getCssVar("--wall");
  ctx.lineWidth = Math.max(2, cellSize * 0.08);

  for (let y = 0; y < gridSize; y++) {
    for (let x = 0; x < gridSize; x++) {
      const cell = maze[y][x];
      const px = x * cellSize;
      const py = y * cellSize;

      if (cell.walls.top) drawLine(px, py, px + cellSize, py);
      if (cell.walls.right) drawLine(px + cellSize, py, px + cellSize, py + cellSize);
      if (cell.walls.bottom) drawLine(px, py + cellSize, px + cellSize, py + cellSize);
      if (cell.walls.left) drawLine(px, py, px, py + cellSize);
    }
  }

  drawExit(performance.now());
  drawPointOrbs();
  drawEnemies();
  drawTrail(performance.now());
  drawPlayer();
  drawScorePopups(performance.now());
  drawFlyingCoins(performance.now());
}

function drawLine(x1, y1, x2, y2) {
  ctx.beginPath();
  ctx.moveTo(x1, y1);
  ctx.lineTo(x2, y2);
  ctx.stroke();
}

function drawPlayer() {
  const cx = renderPlayer.x * cellSize + cellSize / 2;
  const cy = renderPlayer.y * cellSize + cellSize / 2;
  const radius = cellSize * 0.28;

  ctx.shadowBlur = cellSize * 0.35;
  ctx.shadowColor = getCssVar("--player");
  ctx.fillStyle = getCssVar("--player");
  ctx.beginPath();
  ctx.arc(cx, cy, radius, 0, Math.PI * 2);
  ctx.fill();
  ctx.shadowBlur = 0;
}

function drawTrail(now) {
  pruneTrail(now);
  if (trail.length < 3) return;

  const oldest = trail[0];
  const newest = trail[trail.length - 1];
  const startX = oldest.x * cellSize + cellSize / 2;
  const startY = oldest.y * cellSize + cellSize / 2;
  const endX = newest.x * cellSize + cellSize / 2;
  const endY = newest.y * cellSize + cellSize / 2;

  ctx.save();
  ctx.lineCap = "round";
  ctx.lineJoin = "round";
  ctx.lineWidth = Math.max(3, cellSize * 0.2);
  ctx.shadowBlur = cellSize * 0.7;
  const playerRgb = getPlayerRgb();
  ctx.shadowColor = `rgba(${playerRgb.r}, ${playerRgb.g}, ${playerRgb.b}, 0.85)`;

  const gradient = ctx.createLinearGradient(startX, startY, endX, endY);
  gradient.addColorStop(0, "rgba(0, 255, 210, 0)");
  gradient.addColorStop(0.3, "rgba(0, 232, 255, 0.35)");
  gradient.addColorStop(0.7, "rgba(96, 132, 255, 0.68)");
  gradient.addColorStop(1, `rgba(${playerRgb.r}, ${playerRgb.g}, ${playerRgb.b}, 0.95)`);

  ctx.strokeStyle = gradient;
  ctx.beginPath();
  ctx.moveTo(startX, startY);

  for (let i = 1; i < trail.length - 1; i++) {
    const curr = trail[i];
    const next = trail[i + 1];
    const px = curr.x * cellSize + cellSize / 2;
    const py = curr.y * cellSize + cellSize / 2;
    const nx = next.x * cellSize + cellSize / 2;
    const ny = next.y * cellSize + cellSize / 2;
    const midX = (px + nx) / 2;
    const midY = (py + ny) / 2;
    ctx.quadraticCurveTo(px, py, midX, midY);
  }

  ctx.lineTo(endX, endY);
  ctx.stroke();
  ctx.restore();
}

function addTrailPoint(x, y) {
  trail.push({ x, y, createdAt: performance.now() });

  if (trail.length > maxTrailPoints) {
    trail.shift();
  }
}

function drawPointOrbs() {
  for (const orb of pointOrbs) {
    const cx = orb.x * cellSize + cellSize / 2;
    const cy = orb.y * cellSize + cellSize / 2;
    const sizeScale = gridSize >= 80 ? 0.12 : gridSize >= 50 ? 0.16 : 0.22;
    const coinSize = Math.max(4, cellSize * sizeScale);

    ctx.save();
    ctx.textAlign = "center";
    ctx.textBaseline = "middle";
    ctx.font = `${coinSize}px "Segoe UI Emoji", "Apple Color Emoji", sans-serif`;
    ctx.shadowBlur = cellSize * 0.2;
    ctx.shadowColor = "rgba(255, 220, 70, 0.85)";
    ctx.fillText("🪙", cx, cy);
    ctx.restore();
  }
}

function drawScorePopups(now) {
  scorePopups = scorePopups.filter((popup) => now - popup.createdAt < popupDurationMs);

  for (const popup of scorePopups) {
    const age = now - popup.createdAt;
    const t = Math.min(1, age / popupDurationMs);
    const alpha = 1 - t;
    const rise = cellSize * (0.12 + 0.32 * t);
    const x = popup.x * cellSize + cellSize / 2;
    const y = popup.y * cellSize + cellSize / 2 - rise;

    ctx.save();
    ctx.textAlign = "center";
    ctx.textBaseline = "middle";
    ctx.font = `${Math.max(10, cellSize * 0.28)}px "Trebuchet MS", sans-serif`;
    ctx.fillStyle = `rgba(255, 245, 122, ${alpha})`;
    ctx.shadowBlur = cellSize * 0.25;
    ctx.shadowColor = `rgba(255, 240, 100, ${alpha})`;
    ctx.fillText(`+${popup.value}`, x, y);
    ctx.restore();
  }
}

function drawFlyingCoins(now) {
  flyingCoins = flyingCoins.filter((coin) => now - coin.createdAt < coinFlightDurationMs);

  for (const coin of flyingCoins) {
    const age = now - coin.createdAt;
    const t = Math.min(1, age / coinFlightDurationMs);
    const eased = easeOutQuad(t);
    const startX = coin.x * cellSize + cellSize / 2;
    const startY = coin.y * cellSize + cellSize / 2;
    const endY = -cellSize;
    const y = startY + (endY - startY) * eased;
    const drift = Math.sin(t * Math.PI) * cellSize * 0.2;
    const alpha = 1 - t;

    ctx.save();
    ctx.textAlign = "center";
    ctx.textBaseline = "middle";
    ctx.font = `${Math.max(10, cellSize * 0.28)}px "Segoe UI Emoji", "Apple Color Emoji", sans-serif`;
    ctx.globalAlpha = alpha;
    ctx.shadowBlur = cellSize * 0.25;
    ctx.shadowColor = `rgba(255, 220, 70, ${alpha})`;
    ctx.fillText("🪙", startX + drift, y);
    ctx.restore();
  }
}

function drawEnemies() {
  const fontSize = Math.max(12, cellSize * 0.6);
  const hpFontSize = Math.max(9, cellSize * 0.24);
  const revealDistance = isTrollLevel ? 5 : enemyRevealDistance;

  for (const enemy of enemies) {
    const distance = Math.abs(enemy.x - player.x) + Math.abs(enemy.y - player.y);
    if (distance > revealDistance) continue;

    const cx = enemy.x * cellSize + cellSize / 2;
    const cy = enemy.y * cellSize + cellSize / 2;

    ctx.save();
    ctx.textAlign = "center";
    ctx.textBaseline = "middle";
    ctx.font = `${fontSize}px "Segoe UI Emoji", "Apple Color Emoji", sans-serif`;
    ctx.shadowBlur = cellSize * 0.45;
    ctx.shadowColor = "rgba(255, 0, 255, 0.9)";
    ctx.fillText("👾", cx, cy);

    // HP bubble for tactical visibility.
    const bubbleW = Math.max(18, cellSize * 0.48);
    const bubbleH = Math.max(11, cellSize * 0.24);
    const bubbleX = cx - bubbleW / 2;
    const bubbleY = cy - cellSize * 0.48;

    ctx.shadowBlur = 0;
    ctx.fillStyle = "rgba(15, 19, 38, 0.88)";
    ctx.fillRect(bubbleX, bubbleY, bubbleW, bubbleH);
    ctx.strokeStyle = "rgba(255, 110, 255, 0.8)";
    ctx.lineWidth = 1;
    ctx.strokeRect(bubbleX, bubbleY, bubbleW, bubbleH);

    ctx.fillStyle = "#ffd5ff";
    ctx.font = `${hpFontSize}px "Trebuchet MS", sans-serif`;
    ctx.fillText(String(enemy.hp), cx, bubbleY + bubbleH / 2);
    ctx.restore();
  }
}

function pruneTrail(now) {
  trail = trail.filter((point) => now - point.createdAt <= trailLifetimeMs);
}

function drawExit(currentTime = performance.now()) {
  const x = exit.x * cellSize;
  const y = exit.y * cellSize;
  const pad = cellSize * 0.2;
  const cx = x + cellSize / 2;
  const cy = y + cellSize / 2;
  const size = cellSize - pad * 2;
  const radius = size * 0.5;
  const blinkBoost = gridSize >= 60 ? 1.35 : gridSize >= 30 ? 1.15 : 1;

  ctx.save();
  
  // Create blink effect using sine wave (0.5-1 opacity over 1 second cycle)
  const blinkPhase = (currentTime % 1000) / 1000;
  const blinkOpacity = 0.5 + Math.sin(blinkPhase * Math.PI * 2) * 0.5;
  
  ctx.globalAlpha = blinkOpacity;
  ctx.shadowBlur = cellSize * 0.5 * blinkOpacity * blinkBoost;
  ctx.shadowColor = getCssVar("--exit");
  ctx.fillStyle = getCssVar("--exit");

  if (exit.variant === "circle") {
    ctx.beginPath();
    ctx.arc(cx, cy, radius, 0, Math.PI * 2);
    ctx.fill();
  } else if (exit.variant === "diamond") {
    ctx.beginPath();
    ctx.moveTo(cx, y + pad);
    ctx.lineTo(x + cellSize - pad, cy);
    ctx.lineTo(cx, y + cellSize - pad);
    ctx.lineTo(x + pad, cy);
    ctx.closePath();
    ctx.fill();
  } else if (exit.variant === "ring") {
    ctx.lineWidth = Math.max(2, cellSize * 0.16);
    ctx.strokeStyle = getCssVar("--exit");
    ctx.beginPath();
    ctx.arc(cx, cy, radius * 0.85, 0, Math.PI * 2);
    ctx.stroke();
  } else {
    ctx.fillRect(x + pad, y + pad, size, size);
  }

  ctx.restore();
}

function pickExit(distanceMap = null) {
  const candidates = [];

  for (let y = 0; y < gridSize; y++) {
    for (let x = 0; x < gridSize; x++) {
      if (x !== 0 && y !== 0 && x !== gridSize - 1 && y !== gridSize - 1) continue;
      if (x === 0 && y === 0) continue;

      const distance = distanceMap ? distanceMap[y][x] : x + y;
      if (!Number.isFinite(distance)) continue;
      candidates.push({ x, y, distance });
    }
  }

  const sorted = candidates.sort((a, b) => b.distance - a.distance);
  const topSlice = sorted.slice(0, Math.max(3, Math.ceil(sorted.length * 0.25)));
  const chosen = topSlice[Math.floor(Math.random() * topSlice.length)] || sorted[0] || { x: gridSize - 1, y: gridSize - 1 };
  const variant = exitVariants[Math.floor(Math.random() * exitVariants.length)];
  exit = { x: chosen.x, y: chosen.y, variant };
}

function getReachableNeighbors(x, y) {
  const cell = maze[y][x];
  const neighbors = [];

  if (!cell.walls.top && y > 0) neighbors.push({ x, y: y - 1 });
  if (!cell.walls.right && x < gridSize - 1) neighbors.push({ x: x + 1, y });
  if (!cell.walls.bottom && y < gridSize - 1) neighbors.push({ x, y: y + 1 });
  if (!cell.walls.left && x > 0) neighbors.push({ x: x - 1, y });

  return neighbors;
}

function keyFor(x, y) {
  return `${x},${y}`;
}

function findPath(start, end) {
  const queue = [start];
  const cameFrom = new Map();
  const startKey = keyFor(start.x, start.y);
  const endKey = keyFor(end.x, end.y);
  cameFrom.set(startKey, null);

  let head = 0;
  while (head < queue.length) {
    const current = queue[head++];
    const currentKey = keyFor(current.x, current.y);
    if (currentKey === endKey) break;

    for (const next of getReachableNeighbors(current.x, current.y)) {
      const nextKey = keyFor(next.x, next.y);
      if (cameFrom.has(nextKey)) continue;
      cameFrom.set(nextKey, currentKey);
      queue.push(next);
    }
  }

  if (!cameFrom.has(endKey)) return [];

  const path = [];
  let cursor = endKey;
  while (cursor !== null) {
    const [x, y] = cursor.split(",").map(Number);
    path.push({ x, y });
    cursor = cameFrom.get(cursor);
  }

  path.reverse();
  return path;
}

function isCellBlockedForSpawns(x, y) {
  if (x === player.x && y === player.y) return true;
  if (x === exit.x && y === exit.y) return true;
  if (enemies.some((enemy) => enemy.x === x && enemy.y === y)) return true;
  if (pointOrbs.some((orb) => orb.x === x && orb.y === y)) return true;
  return false;
}

function deterministicPointValue(stepIndex, segmentIndex) {
  return 1 + ((stepIndex + segmentIndex) % 4);
}

function buildEnemyCheckpoints(pathLength) {
  if (pathLength < 9) return [];

  const fractions = [0.3, 0.5, 0.7, 0.85];
  let targetCount = Math.max(1, Math.min(4, Math.floor(pathLength / 10)));
  if (isTrollLevel) {
    targetCount = Math.min(5, targetCount + 1);
  }
  const minIndex = 3;
  const maxIndex = pathLength - 2;
  const checkpoints = [];

  for (const fraction of fractions) {
    if (checkpoints.length >= targetCount) break;

    let idx = Math.round((pathLength - 1) * fraction);
    idx = Math.max(minIndex, Math.min(maxIndex, idx));

    if (checkpoints.length > 0 && idx - checkpoints[checkpoints.length - 1] < 3) {
      idx = checkpoints[checkpoints.length - 1] + 3;
    }

    if (idx >= maxIndex) continue;
    checkpoints.push(idx);
  }

  return checkpoints;
}

function buildDistanceMap(start) {
  const distances = Array.from({ length: gridSize }, () => Array(gridSize).fill(Infinity));
  const queue = [start];
  distances[start.y][start.x] = 0;
  let head = 0;

  while (head < queue.length) {
    const current = queue[head++];
    const currentDistance = distances[current.y][current.x];

    for (const next of getReachableNeighbors(current.x, current.y)) {
      if (distances[next.y][next.x] !== Infinity) continue;
      distances[next.y][next.x] = currentDistance + 1;
      queue.push(next);
    }
  }

  return distances;
}

function cellOrderHash(x, y, segmentIndex) {
  return (((x + 1) * 73856093) ^ ((y + 1) * 19349663) ^ ((segmentIndex + 1) * 83492791)) >>> 0;
}

function shuffleCells(cells) {
  const shuffled = cells.slice();

  for (let i = shuffled.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [shuffled[i], shuffled[j]] = [shuffled[j], shuffled[i]];
  }

  return shuffled;
}

function scatterBonusCoins(path) {
  const occupiedKeys = new Set(pointOrbs.map((orb) => keyFor(orb.x, orb.y)));
  const allCells = [];

  for (let y = 0; y < gridSize; y++) {
    for (let x = 0; x < gridSize; x++) {
      if (isCellBlockedForSpawns(x, y)) continue;
      allCells.push({ x, y });
    }
  }

  if (allCells.length === 0) return;

  const density = gridSize >= 80 ? 0.2 : gridSize >= 50 ? 0.24 : 0.3;
  const desiredCoins = Math.max(12, Math.floor(allCells.length * density));
  const scatteredCells = shuffleCells(allCells).filter((cell) => !occupiedKeys.has(keyFor(cell.x, cell.y))).slice(0, desiredCoins);

  for (let i = 0; i < scatteredCells.length; i++) {
    const cell = scatteredCells[i];
    const value = i % 11 === 0 ? 4 : i % 7 === 0 ? 3 : (i % 3 === 0 ? 2 : 1);
    pointOrbs.push({ x: cell.x, y: cell.y, value });
  }
}

function setupPathChallenges() {
  pointOrbs = [];
  enemies = [];

  const path = findPath({ x: 0, y: 0 }, { x: exit.x, y: exit.y });
  if (path.length < 4) return;

  const exitDistance = distancesFromStart[exit.y]?.[exit.x];
  if (!Number.isFinite(exitDistance)) {
    distancesFromStart = buildDistanceMap({ x: 0, y: 0 });
  }
  maxDistanceToExit = distancesFromStart[exit.y][exit.x];
  distanceToExit = maxDistanceToExit;
  playerMaxProgress = maxDistanceToExit;

  const enemyIndices = buildEnemyCheckpoints(path.length);
  let previousEnemyDistance = 0;

  for (let segmentIndex = 0; segmentIndex < enemyIndices.length; segmentIndex++) {
    const enemyIndex = enemyIndices[segmentIndex];
    const enemyCell = path[enemyIndex];
    const enemyDistance = distancesFromStart[enemyCell.y][enemyCell.x];
    const segmentCells = [];

    for (let y = 0; y < gridSize; y++) {
      for (let x = 0; x < gridSize; x++) {
        const d = distancesFromStart[y][x];
        if (!Number.isFinite(d)) continue;
        if (d <= previousEnemyDistance || d >= enemyDistance) continue;
        if (isCellBlockedForSpawns(x, y)) continue;
        segmentCells.push({ x, y, d });
      }
    }

    if (segmentCells.length === 0) continue;

    segmentCells.sort((a, b) => cellOrderHash(a.x, a.y, segmentIndex) - cellOrderHash(b.x, b.y, segmentIndex));
    const density = isTrollLevel ? 0.08 : 0.11;
    const desiredCoins = Math.max(4, Math.min(30, Math.floor(segmentCells.length * density)));

    let segmentPoints = 0;
    for (let i = 0; i < desiredCoins; i++) {
      const cell = segmentCells[i];
      const value = deterministicPointValue(i, segmentIndex);
      pointOrbs.push({ x: cell.x, y: cell.y, value });
      segmentPoints += value;
    }

    if (segmentPoints <= 1) {
      const fallbackCell = segmentCells[0];
      pointOrbs.push({ x: fallbackCell.x, y: fallbackCell.y, value: 2 });
      segmentPoints += 2;
    }

    if (!isCellBlockedForSpawns(enemyCell.x, enemyCell.y) && segmentPoints > 1) {
      // Enemy HP is always lower than available points before it, so full collection guarantees passage.
      const hpPenalty = isTrollLevel ? 0 : 1;
      const hp = Math.max(1, Math.min(40, segmentPoints - hpPenalty));
      enemies.push({ x: enemyCell.x, y: enemyCell.y, hp });
      previousEnemyDistance = enemyDistance;
    }
  }

  scatterBonusCoins(path);
}

function collectPointAt(x, y) {
  const index = pointOrbs.findIndex((orb) => orb.x === x && orb.y === y);
  if (index === -1) return 0;

  const orb = pointOrbs[index];
  pointOrbs.splice(index, 1);
  return orb.value;
}

function findEnemyAt(x, y) {
  return enemies.find((enemy) => enemy.x === x && enemy.y === y) || null;
}

function removeEnemyAt(x, y) {
  const index = enemies.findIndex((enemy) => enemy.x === x && enemy.y === y);
  if (index >= 0) enemies.splice(index, 1);
}

function updateScoreLabel() {
  scoreEl.textContent = `Points: ${playerPoints}`;
}

function updateProgressBar() {
  // Update step counter for impossible mode
  if (difficulty === "impossible") {
    stepsEl.classList.remove("hidden");
    stepsEl.textContent = `Steps: ${stepCount} / ${Math.max(1, optimalPathLength)}`;
  } else {
    stepsEl.classList.add("hidden");
  }
}

function calculateOptimalPath() {
  const path = findPath({ x: 0, y: 0 }, { x: exit.x, y: exit.y });
  return Math.max(1, path.length - 1);
}

function canMoveTo(newX, newY) {
  // Check hard/impossible mode backtracking restriction
  if (difficulty === "hard" || difficulty === "impossible") {
    // If we just moved here, we can't immediately move back
    if (newX === lastPlayerPosition.x && newY === lastPlayerPosition.y) {
      return false;
    }
  }

  // Check impossible mode step limit
  if (difficulty === "impossible" && stepCount >= optimalPathLength) {
    return false;
  }

  return true;
}

function showHomeMenu() {
  homeMenu.classList.remove("hidden");
  homeMenu.setAttribute("aria-hidden", "false");
}

function hideHomeMenu() {
  homeMenu.classList.add("hidden");
  homeMenu.setAttribute("aria-hidden", "true");
}

function startGameWithDifficulty(selectedDifficulty) {
  difficulty = selectedDifficulty;
  hideHomeMenu();
  stepCount = 0;
  gridSize = Number(sizeSelect.value);
  isTrollLevel = gridSize === 25;
  document.body.classList.toggle("troll-mode", isTrollLevel);
  if (isTrollLevel) {
    startTrollAmbience();
  } else {
    stopTrollAmbience();
    clearTrollIdlePopupTimer();
  }
  cellSize = canvas.width / gridSize;
  player = { x: 0, y: 0 };
  renderPlayer = { x: 0, y: 0 };
  lastPlayerPosition = { x: 0, y: 0 };
  if (fadeFrameId !== null) {
    cancelAnimationFrame(fadeFrameId);
    fadeFrameId = null;
  }
  moveQueue.length = 0;
  playerPoints = 0;
  enemies = [];
  scorePopups = [];
  flyingCoins = [];
  trail = [];
  addTrailPoint(renderPlayer.x, renderPlayer.y);
  gameWon = false;
  isAnimatingMove = false;
  
  let message = "Reach the exit!";
  if (difficulty === "easy") {
    message = "Easy Mode: Collect coins and reach the exit!";
  } else if (difficulty === "hard") {
    message = "Hard Mode: No moving backward!";
  } else if (difficulty === "impossible") {
    message = "Impossible Mode: Limited steps + no going back!";
  }

  statusEl.textContent = isTrollLevel && message.includes("Reach the exit!")
    ? "TROLL LEVEL 25x25: collect smart, enemies are harsher."
    : message;
  hideWinPopup();
  hideTrollPopup();
  updateScoreLabel();
  initMaze();
  distancesFromStart = buildDistanceMap({ x: 0, y: 0 });
  pickExit(distancesFromStart);
  setupPathChallenges();
  
  // Calculate optimal path for impossible mode
  if (difficulty === "impossible") {
    optimalPathLength = calculateOptimalPath();
  } else {
    optimalPathLength = 0;
  }
  
  updateProgressBar();
  drawMaze();

  if (isTrollLevel) {
    scheduleTrollIdlePopup();
  }
}

function showWinPopup() {
  winOverlayEl.setAttribute("aria-hidden", "false");
  winPopupEl.classList.add("show");
}

function hideWinPopup() {
  winOverlayEl.setAttribute("aria-hidden", "true");
  winPopupEl.classList.remove("show");
}

function showWelcome() {
  gameStarted = false;
  welcomeOverlayEl.classList.remove("hidden");
  welcomeOverlayEl.setAttribute("aria-hidden", "false");
  // Reset progress bar
  distanceToExit = Infinity;
  maxDistanceToExit = Infinity;
  updateProgressBar();
}

function hideWelcome() {
  welcomeOverlayEl.classList.add("hidden");
  welcomeOverlayEl.setAttribute("aria-hidden", "true");
}

function openThemeModal() {
  themeModal.classList.remove("hidden");
  themeModal.setAttribute("aria-hidden", "false");
}

function closeThemeModal() {
  themeModal.classList.add("hidden");
  themeModal.setAttribute("aria-hidden", "true");
}

function showTrollPopup() {
  const randomTiltDeg = (Math.random() * 14 - 7).toFixed(2);
  const randomDurationMs = 900 + Math.floor(Math.random() * 1000);

  trollPopupEl.textContent = "👹";
  trollPopupEl.style.setProperty("--troll-rotate", `${randomTiltDeg}deg`);
  trollOverlayEl.setAttribute("aria-hidden", "false");
  trollPopupEl.classList.add("show");

  if (trollPopupTimeoutId !== null) {
    window.clearTimeout(trollPopupTimeoutId);
  }

  trollPopupTimeoutId = window.setTimeout(() => {
    hideTrollPopup();
  }, randomDurationMs);
}

function hideTrollPopup() {
  if (trollPopupTimeoutId !== null) {
    window.clearTimeout(trollPopupTimeoutId);
    trollPopupTimeoutId = null;
  }
  trollOverlayEl.setAttribute("aria-hidden", "true");
  trollPopupEl.classList.remove("show");
}

function clearTrollIdlePopupTimer() {
  if (trollIdlePopupTimeoutId !== null) {
    window.clearTimeout(trollIdlePopupTimeoutId);
    trollIdlePopupTimeoutId = null;
  }
}

function scheduleTrollIdlePopup() {
  if (!isTrollLevel) return;

  clearTrollIdlePopupTimer();
  const waitMs = 5000 + Math.floor(Math.random() * 5001);
  trollIdlePopupTimeoutId = window.setTimeout(() => {
    trollIdlePopupTimeoutId = null;
    showTrollPopup();
    playTrollBooSound();
  }, waitMs);
}

function noteTrollActivity() {
  if (!isTrollLevel) return;
  hideTrollPopup();
  scheduleTrollIdlePopup();
}

function addScorePopup(x, y, value) {
  scorePopups.push({ x, y, value, createdAt: performance.now() });
}

function addFlyingCoin(x, y) {
  flyingCoins.push({ x, y, createdAt: performance.now() });
}

function playCoinSound(value) {
  const AudioCtx = window.AudioContext || window.webkitAudioContext;
  if (!AudioCtx) return;
  if (!audioContext) {
    audioContext = new AudioCtx();
  }

  const now = audioContext.currentTime;
  const gain = audioContext.createGain();
  gain.connect(audioContext.destination);
  gain.gain.setValueAtTime(0.0001, now);
  gain.gain.exponentialRampToValueAtTime(0.16, now + 0.01);
  gain.gain.exponentialRampToValueAtTime(0.0001, now + 0.18);

  const oscA = audioContext.createOscillator();
  const oscB = audioContext.createOscillator();
  oscA.type = "triangle";
  oscB.type = "sine";
  const base = 620 + Math.min(260, value * 24);
  oscA.frequency.setValueAtTime(base, now);
  oscA.frequency.exponentialRampToValueAtTime(base * 1.42, now + 0.16);
  oscB.frequency.setValueAtTime(base * 2, now);
  oscB.frequency.exponentialRampToValueAtTime(base * 2.4, now + 0.16);

  oscA.connect(gain);
  oscB.connect(gain);
  oscA.start(now);
  oscB.start(now);
  oscA.stop(now + 0.2);
  oscB.stop(now + 0.2);
}

function ensureAudioContext() {
  const AudioCtx = window.AudioContext || window.webkitAudioContext;
  if (!AudioCtx) return null;

  if (!audioContext) {
    audioContext = new AudioCtx();
  }

  if (audioContext.state === "suspended") {
    audioContext.resume();
  }

  return audioContext;
}

function startTrollAmbience() {
  const ctxAudio = ensureAudioContext();
  if (!ctxAudio || trollAmbientNodes) return;

  const master = ctxAudio.createGain();
  master.gain.value = 0.045;
  master.connect(ctxAudio.destination);

  const droneA = ctxAudio.createOscillator();
  droneA.type = "sawtooth";
  droneA.frequency.value = 47;

  const droneB = ctxAudio.createOscillator();
  droneB.type = "triangle";
  droneB.frequency.value = 63;

  const droneGain = ctxAudio.createGain();
  droneGain.gain.value = 0.2;

  const filter = ctxAudio.createBiquadFilter();
  filter.type = "lowpass";
  filter.frequency.value = 340;
  filter.Q.value = 2.2;

  const tremoloOsc = ctxAudio.createOscillator();
  tremoloOsc.type = "sine";
  tremoloOsc.frequency.value = 0.7;
  const tremoloGain = ctxAudio.createGain();
  tremoloGain.gain.value = 0.12;

  droneA.connect(droneGain);
  droneB.connect(droneGain);
  droneGain.connect(filter);
  filter.connect(master);
  tremoloOsc.connect(tremoloGain);
  tremoloGain.connect(master.gain);

  const now = ctxAudio.currentTime;
  droneA.start(now);
  droneB.start(now);
  tremoloOsc.start(now);

  trollAmbientNodes = {
    master,
    droneA,
    droneB,
    droneGain,
    filter,
    tremoloOsc,
    tremoloGain,
  };

  trollPulseIntervalId = window.setInterval(() => {
    if (!audioContext || !trollAmbientNodes) return;
    const t = audioContext.currentTime;
    const f = trollAmbientNodes.filter.frequency;
    const base = 260 + Math.random() * 180;
    f.cancelScheduledValues(t);
    f.setValueAtTime(base, t);
    f.linearRampToValueAtTime(base + 90 + Math.random() * 70, t + 0.35);
  }, 1200);
}

function stopTrollAmbience() {
  if (!trollAmbientNodes || !audioContext) return;

  const t = audioContext.currentTime;
  trollAmbientNodes.master.gain.cancelScheduledValues(t);
  trollAmbientNodes.master.gain.setValueAtTime(trollAmbientNodes.master.gain.value, t);
  trollAmbientNodes.master.gain.exponentialRampToValueAtTime(0.0001, t + 0.2);

  trollAmbientNodes.droneA.stop(t + 0.22);
  trollAmbientNodes.droneB.stop(t + 0.22);
  trollAmbientNodes.tremoloOsc.stop(t + 0.22);

  if (trollPulseIntervalId !== null) {
    window.clearInterval(trollPulseIntervalId);
    trollPulseIntervalId = null;
  }

  trollAmbientNodes = null;
}

function playTrollThreatSound() {
  if (!isTrollLevel) return;
  const ctxAudio = ensureAudioContext();
  if (!ctxAudio) return;

  const now = ctxAudio.currentTime;
  const gain = ctxAudio.createGain();
  gain.connect(ctxAudio.destination);
  gain.gain.setValueAtTime(0.0001, now);
  gain.gain.exponentialRampToValueAtTime(0.09, now + 0.02);
  gain.gain.exponentialRampToValueAtTime(0.0001, now + 0.3);

  const osc = ctxAudio.createOscillator();
  osc.type = "square";
  osc.frequency.setValueAtTime(220, now);
  osc.frequency.exponentialRampToValueAtTime(96, now + 0.3);
  osc.connect(gain);
  osc.start(now);
  osc.stop(now + 0.31);
}

function playTrollBooSound() {
  if (!isTrollLevel) return;
  const ctxAudio = ensureAudioContext();
  if (!ctxAudio) return;

  const now = ctxAudio.currentTime;
  const duration = 0.75 + Math.random() * 0.55;
  const freqAStart = 360 + Math.random() * 200;
  const freqAEnd = 70 + Math.random() * 55;
  const freqBStart = 190 + Math.random() * 160;
  const freqBEnd = 48 + Math.random() * 42;

  const gain = ctxAudio.createGain();
  gain.connect(ctxAudio.destination);
  gain.gain.setValueAtTime(0.0001, now);
  gain.gain.exponentialRampToValueAtTime(0.14, now + 0.04);
  gain.gain.exponentialRampToValueAtTime(0.0001, now + duration);

  const filter = ctxAudio.createBiquadFilter();
  filter.type = "bandpass";
  filter.frequency.setValueAtTime(500 + Math.random() * 800, now);
  filter.Q.value = 2.6;
  filter.connect(gain);

  const oscA = ctxAudio.createOscillator();
  const oscB = ctxAudio.createOscillator();
  const lfo = ctxAudio.createOscillator();
  const lfoGain = ctxAudio.createGain();
  oscA.type = "sawtooth";
  oscB.type = "square";
  oscA.frequency.setValueAtTime(freqAStart, now);
  oscA.frequency.exponentialRampToValueAtTime(freqAEnd, now + duration);
  oscB.frequency.setValueAtTime(freqBStart, now);
  oscB.frequency.exponentialRampToValueAtTime(freqBEnd, now + duration);

  lfo.type = "sine";
  lfo.frequency.setValueAtTime(6 + Math.random() * 5, now);
  lfoGain.gain.setValueAtTime(7 + Math.random() * 7, now);
  lfo.connect(lfoGain);
  lfoGain.connect(oscA.frequency);
  lfoGain.connect(oscB.frequency);

  const noiseDuration = duration * 0.95;
  const noiseBuffer = ctxAudio.createBuffer(1, Math.floor(ctxAudio.sampleRate * noiseDuration), ctxAudio.sampleRate);
  const noiseData = noiseBuffer.getChannelData(0);
  for (let i = 0; i < noiseData.length; i++) {
    noiseData[i] = (Math.random() * 2 - 1) * (1 - i / noiseData.length);
  }
  const noise = ctxAudio.createBufferSource();
  noise.buffer = noiseBuffer;

  const noiseGain = ctxAudio.createGain();
  noiseGain.gain.setValueAtTime(0.0001, now);
  noiseGain.gain.exponentialRampToValueAtTime(0.09, now + 0.06);
  noiseGain.gain.exponentialRampToValueAtTime(0.0001, now + noiseDuration);

  oscA.connect(filter);
  oscB.connect(filter);
  noise.connect(noiseGain);
  noiseGain.connect(filter);

  oscA.start(now);
  oscB.start(now);
  lfo.start(now);
  noise.start(now);
  oscA.stop(now + duration + 0.02);
  oscB.stop(now + duration + 0.02);
  lfo.stop(now + duration + 0.02);
  noise.stop(now + noiseDuration + 0.02);
}

function tryMove(dx, dy) {
  if (gameWon || isAnimatingMove) return;

  const cell = maze[player.y][player.x];

  if (dx === 1 && cell.walls.right) return restartOnWallHit();
  if (dx === -1 && cell.walls.left) return restartOnWallHit();
  if (dy === 1 && cell.walls.bottom) return restartOnWallHit();
  if (dy === -1 && cell.walls.top) return restartOnWallHit();

  const nx = player.x + dx;
  const ny = player.y + dy;

  if (nx < 0 || nx >= gridSize || ny < 0 || ny >= gridSize) return restartOnWallHit();

  // Check if movement is allowed in current difficulty
  if (!canMoveTo(nx, ny)) {
    if (difficulty === "hard" || difficulty === "impossible") {
      statusEl.textContent = "You can't move backward!";
    } else if (difficulty === "impossible" && stepCount >= optimalPathLength) {
      statusEl.textContent = `Out of steps! Max was ${optimalPathLength}.`;
    }
    return;
  }

  const enemy = findEnemyAt(nx, ny);
  if (enemy) {
    if (playerPoints <= enemy.hp) {
      statusEl.textContent = `Enemy HP ${enemy.hp}. You need more than ${enemy.hp} points to pass.`;
      playTrollThreatSound();
      drawMaze();
      return;
    }

    playerPoints -= enemy.hp;
    removeEnemyAt(nx, ny);
    updateScoreLabel();
    statusEl.textContent = `Enemy defeated! -${enemy.hp} points.`;
  }

  const start = { x: player.x, y: player.y };
  lastPlayerPosition = { x: player.x, y: player.y };
  player.x = nx;
  player.y = ny;
  
  // Track steps for impossible mode
  if (difficulty === "impossible" || difficulty === "hard") {
    stepCount++;
  }

  // Update distance to exit for progress bar
  if (Number.isFinite(distancesFromStart[player.y][player.x])) {
    distanceToExit = distancesFromStart[player.y][player.x];
  }

  const gained = collectPointAt(player.x, player.y);
  if (gained > 0) {
    playerPoints += gained;
    updateScoreLabel();
    statusEl.textContent = `+${gained} points collected.`;
    addScorePopup(player.x, player.y, gained);
    addFlyingCoin(player.x, player.y);
    playCoinSound(gained);
    startFadeLoop();
  }

  if (player.x === exit.x && player.y === exit.y) {
    gameWon = true;
    statusEl.textContent = `You escaped with ${playerPoints} points! Click New Maze to play again.`;
    showWinPopup();
  } else {
    if (gained === 0 && !enemy) {
      statusEl.textContent = "Keep going...";
    }
  }

  updateProgressBar();
  animatePlayerMove(start, { x: nx, y: ny });
}

function queueMove(dx, dy) {
  if (gameWon) return;

  if (isAnimatingMove) {
    if (moveQueue.length < maxQueuedMoves) {
      moveQueue.push({ dx, dy });
    }
    return;
  }

  tryMove(dx, dy);
}

function restartOnWallHit() {
  moveQueue.length = 0;
  startNewGame("You hit a wall. Maze restarted!");
}

function animatePlayerMove(from, to) {
  isAnimatingMove = true;
  const startTime = performance.now();

  function frame(now) {
    const elapsed = now - startTime;
    const t = Math.min(1, elapsed / moveDurationMs);
    const eased = easeOutQuad(t);

    renderPlayer.x = from.x + (to.x - from.x) * eased;
    renderPlayer.y = from.y + (to.y - from.y) * eased;
    addTrailPoint(renderPlayer.x, renderPlayer.y);
    drawMaze();

    if (t < 1) {
      requestAnimationFrame(frame);
      return;
    }

    renderPlayer.x = to.x;
    renderPlayer.y = to.y;
    isAnimatingMove = false;
    drawMaze();

    if (moveQueue.length > 0) {
      const nextMove = moveQueue.shift();
      queueMove(nextMove.dx, nextMove.dy);
    } else {
      startFadeLoop();
    }
  }

  requestAnimationFrame(frame);
}

function easeOutQuad(t) {
  if (t < 0.5) {
    return 4 * t * t * t;
  }
  return 1 - Math.pow(-2 * t + 2, 3) / 2;
}

function onKeyDown(event) {
  const key = event.key.toLowerCase();

  // Check for Escape key to close theme modal
  if (key === "escape" && !themeModal.classList.contains("hidden")) {
    closeThemeModal();
    event.preventDefault();
    return;
  }

  // Check for 'm' key to start new game from welcome screen
  if (key === "m" && !welcomeOverlayEl.classList.contains("hidden")) {
    startNewGame();
    event.preventDefault();
    return;
  }

  if (["arrowup", "arrowdown", "arrowleft", "arrowright", "w", "a", "s", "d"].includes(key)) {
    event.preventDefault();
    noteTrollActivity();
  }

  if (key === "arrowup" || key === "w") queueMove(0, -1);
  if (key === "arrowdown" || key === "s") queueMove(0, 1);
  if (key === "arrowleft" || key === "a") queueMove(-1, 0);
  if (key === "arrowright" || key === "d") queueMove(1, 0);
}

function onTouchStart(event) {
  if (event.touches.length === 0) return;
  const touch = event.touches[0];
  touchStart = { x: touch.clientX, y: touch.clientY };
  noteTrollActivity();
  event.preventDefault();
}

function onTouchMove(event) {
  event.preventDefault();
}

function onTouchEnd(event) {
  if (!touchStart || event.changedTouches.length === 0) return;

  const touch = event.changedTouches[0];
  const dx = touch.clientX - touchStart.x;
  const dy = touch.clientY - touchStart.y;
  const absX = Math.abs(dx);
  const absY = Math.abs(dy);
  const minSwipeDistance = 24;

  touchStart = null;
  event.preventDefault();

  if (Math.max(absX, absY) < minSwipeDistance) return;

  if (absX > absY) {
    queueMove(dx > 0 ? 1 : -1, 0);
    return;
  }

  queueMove(0, dy > 0 ? 1 : -1);
}

function startFadeLoop() {
  if (fadeFrameId !== null) return;

  function tick(now) {
    pruneTrail(now);
    scorePopups = scorePopups.filter((popup) => now - popup.createdAt < popupDurationMs);
    flyingCoins = flyingCoins.filter((coin) => now - coin.createdAt < coinFlightDurationMs);
    drawMaze();

    if ((trail.length > 1 || scorePopups.length > 0 || flyingCoins.length > 0) && !isAnimatingMove) {
      fadeFrameId = requestAnimationFrame(tick);
      return;
    }

    fadeFrameId = null;
  }

  fadeFrameId = requestAnimationFrame(tick);
}

function getCssVar(name) {
  return getComputedStyle(document.documentElement).getPropertyValue(name).trim();
}

function hexToRgb(hexColor) {
  const hex = hexColor.replace("#", "").trim();
  const fullHex = hex.length === 3
    ? hex.split("").map((c) => c + c).join("")
    : hex;

  const intValue = Number.parseInt(fullHex, 16);
  return {
    r: (intValue >> 16) & 255,
    g: (intValue >> 8) & 255,
    b: intValue & 255,
  };
}

function getPlayerRgb() {
  return hexToRgb(getCssVar("--player"));
}

const themes = {
  "laser-red": {
    "--wall": "#ff2e2e",
    "--exit": "#ff6b6b",
    "--player": "#ff3b3b",
    "--accent": "#ff1744",
    "--bg": "#1a0b0b",
    "--panel": "#2a1414",
    "--ink": "#ffcccc",
    "--path": "#0f0505",
    "--trail-rgb": "255, 100, 100",
    "--bg-glow-a": "rgba(120, 20, 20, 0.9)",
    "--bg-glow-b": "rgba(70, 10, 10, 0.8)",
    "--panel-glow": "rgba(255, 46, 99, 0.25)",
    "--board-glow": "rgba(255, 46, 99, 0.22)",
  },
  "neon-yellow": {
    "--wall": "#ffea00",
    "--exit": "#ffd600",
    "--player": "#ffeb3b",
    "--accent": "#ffb300",
    "--bg": "#1a1600",
    "--panel": "#2a2410",
    "--ink": "#fffacd",
    "--path": "#0f0a00",
    "--trail-rgb": "255, 230, 0",
    "--bg-glow-a": "rgba(120, 100, 0, 0.88)",
    "--bg-glow-b": "rgba(70, 55, 0, 0.8)",
    "--panel-glow": "rgba(255, 214, 0, 0.24)",
    "--board-glow": "rgba(255, 214, 0, 0.2)",
  },
  "electric-lime": {
    "--wall": "#39ff14",
    "--exit": "#7fff00",
    "--player": "#76ff03",
    "--accent": "#00ff00",
    "--bg": "#0a1400",
    "--panel": "#141f0a",
    "--ink": "#e8ffcc",
    "--path": "#050a00",
    "--trail-rgb": "57, 255, 20",
    "--bg-glow-a": "rgba(20, 90, 10, 0.88)",
    "--bg-glow-b": "rgba(10, 50, 6, 0.8)",
    "--panel-glow": "rgba(57, 255, 20, 0.24)",
    "--board-glow": "rgba(57, 255, 20, 0.2)",
  },
  "cyber-cyan": {
    "--wall": "#00e5ff",
    "--exit": "#00bcd4",
    "--player": "#00d4ff",
    "--accent": "#00c2ff",
    "--bg": "#070912",
    "--panel": "#0b1020",
    "--ink": "#d9f8ff",
    "--path": "#05070f",
    "--trail-rgb": "0, 255, 220",
    "--bg-glow-a": "rgba(16, 39, 72, 0.9)",
    "--bg-glow-b": "rgba(40, 15, 71, 0.75)",
    "--panel-glow": "rgba(0, 194, 255, 0.25)",
    "--board-glow": "rgba(0, 194, 255, 0.2)",
  },
  "hot-magenta": {
    "--wall": "#ff00ff",
    "--exit": "#ff1493",
    "--player": "#ff0080",
    "--accent": "#ff006e",
    "--bg": "#1a0a1a",
    "--panel": "#240d24",
    "--ink": "#ffccff",
    "--path": "#0f0410",
    "--trail-rgb": "255, 50, 200",
    "--bg-glow-a": "rgba(90, 20, 80, 0.88)",
    "--bg-glow-b": "rgba(60, 10, 50, 0.8)",
    "--panel-glow": "rgba(255, 0, 255, 0.24)",
    "--board-glow": "rgba(255, 0, 255, 0.2)",
  },
  "plasma-orange": {
    "--wall": "#ff8c00",
    "--exit": "#ff6347",
    "--player": "#ffa500",
    "--accent": "#ff7f00",
    "--bg": "#1a0f08",
    "--panel": "#2a1810",
    "--ink": "#ffd9b3",
    "--path": "#0f0804",
    "--trail-rgb": "255, 140, 0",
    "--bg-glow-a": "rgba(110, 60, 10, 0.88)",
    "--bg-glow-b": "rgba(70, 35, 10, 0.8)",
    "--panel-glow": "rgba(255, 140, 0, 0.24)",
    "--board-glow": "rgba(255, 140, 0, 0.2)",
  },
  "toxic-green": {
    "--wall": "#00ff41",
    "--exit": "#39ff14",
    "--player": "#00ff00",
    "--accent": "#00ff00",
    "--bg": "#051205",
    "--panel": "#0a1a0a",
    "--ink": "#ccffcc",
    "--path": "#020805",
    "--trail-rgb": "0, 255, 65",
    "--bg-glow-a": "rgba(0, 70, 30, 0.88)",
    "--bg-glow-b": "rgba(0, 40, 18, 0.8)",
    "--panel-glow": "rgba(0, 255, 65, 0.24)",
    "--board-glow": "rgba(0, 255, 65, 0.2)",
  },
  "arctic-ice": {
    "--wall": "#00f0ff",
    "--exit": "#0ff0ff",
    "--player": "#00ffff",
    "--accent": "#00dddd",
    "--bg": "#050a0f",
    "--panel": "#0a1420",
    "--ink": "#b3f0ff",
    "--path": "#020508",
    "--trail-rgb": "100, 240, 255",
    "--bg-glow-a": "rgba(12, 70, 95, 0.88)",
    "--bg-glow-b": "rgba(8, 38, 60, 0.8)",
    "--panel-glow": "rgba(0, 240, 255, 0.24)",
    "--board-glow": "rgba(0, 240, 255, 0.2)",
  },
  "sunset-fire": {
    "--wall": "#ff4500",
    "--exit": "#ff6347",
    "--player": "#ff7f50",
    "--accent": "#ff6347",
    "--bg": "#1a0a00",
    "--panel": "#2a1410",
    "--ink": "#ffccb3",
    "--path": "#0f0500",
    "--trail-rgb": "255, 100, 50",
    "--bg-glow-a": "rgba(110, 35, 10, 0.88)",
    "--bg-glow-b": "rgba(70, 20, 8, 0.8)",
    "--panel-glow": "rgba(255, 69, 0, 0.24)",
    "--board-glow": "rgba(255, 69, 0, 0.2)",
  },
  "deep-purple": {
    "--wall": "#9d4edd",
    "--exit": "#bb86fc",
    "--player": "#b39ddb",
    "--accent": "#ab47bc",
    "--bg": "#0f0a15",
    "--panel": "#1a1428",
    "--ink": "#e1bee7",
    "--path": "#0a050f",
    "--trail-rgb": "157, 78, 221",
    "--bg-glow-a": "rgba(58, 24, 86, 0.88)",
    "--bg-glow-b": "rgba(28, 14, 44, 0.8)",
    "--panel-glow": "rgba(157, 78, 221, 0.24)",
    "--board-glow": "rgba(157, 78, 221, 0.2)",
  },
  "rainbow": {
    "--wall": "#ff0080",
    "--exit": "#00ff00",
    "--player": "#00ffff",
    "--accent": "#ffff00",
    "--bg": "#0a0a0a",
    "--panel": "#1a1a1a",
    "--ink": "#ffffff",
    "--path": "#050505",
    "--trail-rgb": "255, 100, 255",
    "--bg-glow-a": "rgba(120, 0, 80, 0.9)",
    "--bg-glow-b": "rgba(0, 120, 120, 0.82)",
    "--panel-glow": "rgba(255, 255, 255, 0.24)",
    "--board-glow": "rgba(255, 255, 255, 0.18)",
  },
};

function applyTheme(themeName) {
  const theme = themes[themeName];
  if (!theme) return;
  
  currentTheme = themeName;
  
  // Remove rainbow mode class if it was active
  document.body.classList.remove("rainbow-mode");
  
  // Add rainbow mode class if rainbow theme is selected
  if (themeName === "rainbow") {
    document.body.classList.add("rainbow-mode");
  }
  
  for (const [varName, varValue] of Object.entries(theme)) {
    document.documentElement.style.setProperty(varName, varValue);
  }
  
  // Update active button styling
  themeBtns.forEach(btn => {
    if (btn.getAttribute("data-theme") === themeName) {
      btn.classList.add("active");
    } else {
      btn.classList.remove("active");
    }
  });
  
  // Close modal after theme selection with smooth animation
  setTimeout(() => {
    closeThemeModal();
  }, 100);
  
  drawMaze();
}

function setPlayerColor(hexColor) {
  document.documentElement.style.setProperty("--player", hexColor);
  drawMaze();
}

function startNewGame(message = "Reach the exit!") {
  // This function is deprecated - use startGameWithDifficulty instead
  // Kept for backwards compatibility
  startGameWithDifficulty(difficulty || "easy");
}

newGameBtn.addEventListener("click", () => showHomeMenu());
sizeSelect.addEventListener("change", () => showHomeMenu());
easyBtn.addEventListener("click", () => startGameWithDifficulty("easy"));
hardBtn.addEventListener("click", () => startGameWithDifficulty("hard"));
impossibleBtn.addEventListener("click", () => startGameWithDifficulty("impossible"));
themeBtn.addEventListener("click", () => openThemeModal());
themeModalClose.addEventListener("click", () => closeThemeModal());
themeModalOverlay.addEventListener("click", () => closeThemeModal());
themeBtns.forEach(btn => {
  btn.addEventListener("click", () => {
    const themeName = btn.getAttribute("data-theme");
    applyTheme(themeName);
  });
});
window.addEventListener("keydown", onKeyDown);
canvas.addEventListener("touchstart", onTouchStart, { passive: false });
canvas.addEventListener("touchmove", onTouchMove, { passive: false });
canvas.addEventListener("touchend", onTouchEnd, { passive: false });
window.addEventListener("pointerdown", () => {
  if (isTrollLevel) startTrollAmbience();
}, { once: false });

applyTheme(currentTheme);
showHomeMenu();
