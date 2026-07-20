import { useState, useEffect, useCallback, useRef } from "react";

const ROWS = 6;
const COLS = 7;
const EMPTY = 0;
const HUMAN = 1;
const BOT = 2;

// ── Difficulty configuration ────────────────────────────────────────────────
// Easy/Medium can blunder or skip blocks on purpose. Hard rarely does.
// "Impossible" never blunders and always takes an immediate win/block, then
// searches as deep as the time budget allows. NOTE (see chat): this is a
// strong heuristic alpha-beta search, not a fully solved Connect Four oracle
// (that requires reasoning about all ~4.5 trillion positions / up to 42-ply
// lines). It plays extremely well but is not mathematically unbeatable.
const DIFFICULTIES = {
  Easy:       { maxDepth: 2,  timeMs: 150,  blockChance: 0.45, randomChance: 0.40 },
  Medium:     { maxDepth: 4,  timeMs: 300,  blockChance: 0.80, randomChance: 0.15 },
  Hard:       { maxDepth: 7,  timeMs: 700,  blockChance: 1.00, randomChance: 0.03 },
  Impossible: { maxDepth: 15, timeMs: 2200, blockChance: 1.00, randomChance: 0 },
};
const DIFFICULTY_ORDER = ["Easy", "Medium", "Hard", "Impossible"];
const MOVE_LIMIT_OPTIONS = [
  { label: "Off", value: null },
  { label: "10s", value: 10 },
  { label: "20s", value: 20 },
  { label: "30s", value: 30 },
];

const idx = (r, c) => r * COLS + c;
const createBoard = () => new Array(ROWS * COLS).fill(EMPTY);
const cloneBoard = (b) => [...b];

const getRow = (b, col) => {
  for (let r = ROWS - 1; r >= 0; r--) if (b[idx(r, col)] === EMPTY) return r;
  return -1;
};
const getValidCols = (b) => {
  const cols = [];
  for (let c = 0; c < COLS; c++) if (b[idx(0, c)] === EMPTY) cols.push(c);
  return cols;
};
const dropMut = (b, col, player) => {
  const r = getRow(b, col);
  if (r === -1) return -1;
  b[idx(r, col)] = player;
  return r;
};
const undrop = (b, col, row) => { b[idx(row, col)] = EMPTY; };

const checkWinAt = (b, row, col, player) => {
  const dirs = [[0,1],[1,0],[1,1],[1,-1]];
  for (const [dr, dc] of dirs) {
    let count = 1;
    const cells = [[row, col]];
    for (let d = 1; d <= 3; d++) {
      const r = row + dr*d, c = col + dc*d;
      if (r<0||r>=ROWS||c<0||c>=COLS||b[idx(r,c)]!==player) break;
      cells.push([r,c]); count++;
    }
    for (let d = 1; d <= 3; d++) {
      const r = row - dr*d, c = col - dc*d;
      if (r<0||r>=ROWS||c<0||c>=COLS||b[idx(r,c)]!==player) break;
      cells.push([r,c]); count++;
    }
    if (count >= 4) return cells;
  }
  return null;
};

const POS_W = [
  3,4,5,7,5,4,3,
  4,6,8,10,8,6,4,
  5,7,11,13,11,7,5,
  5,7,11,13,11,7,5,
  4,6,8,10,8,6,4,
  3,4,5,7,5,4,3,
];

const scoreWindow4 = (a, b, c, d) => {
  let bot=0, hum=0;
  for (const v of [a,b,c,d]) { if(v===BOT) bot++; else if(v===HUMAN) hum++; }
  if(bot===4) return 500000;
  if(hum===4) return -500000;
  if(bot===3&&hum===0) return 60;
  if(bot===2&&hum===0) return 12;
  if(hum===3&&bot===0) return -200;
  if(hum===2&&bot===0) return -15;
  return 0;
};

const staticScore = (b) => {
  let s = 0;
  for (let i = 0; i < ROWS*COLS; i++) {
    if (b[i]===BOT) s += POS_W[i];
    else if (b[i]===HUMAN) s -= POS_W[i];
  }
  for (let r=0;r<ROWS;r++) for (let c=0;c<=COLS-4;c++) s+=scoreWindow4(b[idx(r,c)],b[idx(r,c+1)],b[idx(r,c+2)],b[idx(r,c+3)]);
  for (let c=0;c<COLS;c++) for (let r=0;r<=ROWS-4;r++) s+=scoreWindow4(b[idx(r,c)],b[idx(r+1,c)],b[idx(r+2,c)],b[idx(r+3,c)]);
  for (let r=0;r<=ROWS-4;r++) for (let c=0;c<=COLS-4;c++) s+=scoreWindow4(b[idx(r,c)],b[idx(r+1,c+1)],b[idx(r+2,c+2)],b[idx(r+3,c+3)]);
  for (let r=0;r<=ROWS-4;r++) for (let c=3;c<COLS;c++) s+=scoreWindow4(b[idx(r,c)],b[idx(r+1,c-1)],b[idx(r+2,c-2)],b[idx(r+3,c-3)]);
  return s;
};

const COL_ORDER = [3,2,4,1,5,0,6];

class TimeUp extends Error {}
let nodeCount = 0;

const minimax = (b, depth, alpha, beta, maximizing, deadline) => {
  nodeCount++;
  if (deadline && (nodeCount & 511) === 0 && performance.now() > deadline) throw new TimeUp();

  const valid = COL_ORDER.filter(c => b[idx(0,c)] === EMPTY);
  if (!valid.length) return { score: 0 };
  if (depth === 0) return { score: staticScore(b) };
  const player = maximizing ? BOT : HUMAN;
  const opp    = maximizing ? HUMAN : BOT;
  const wins = [], blocks = [], rest = [];
  for (const c of valid) {
    const r = getRow(b, c);
    b[idx(r,c)] = player; const iw = !!checkWinAt(b,r,c,player); b[idx(r,c)] = EMPTY;
    if (iw) { wins.push(c); continue; }
    b[idx(r,c)] = opp;   const ib = !!checkWinAt(b,r,c,opp);    b[idx(r,c)] = EMPTY;
    if (ib) { blocks.push(c); continue; }
    rest.push(c);
  }
  const ordered = [...wins, ...blocks, ...rest];
  if (maximizing) {
    let best = { score: -Infinity, col: ordered[0] };
    for (const col of ordered) {
      const r = dropMut(b, col, BOT);
      const win = checkWinAt(b, r, col, BOT);
      let score;
      if (win) score = 1000000 + depth;
      else if (!getValidCols(b).length) score = 0;
      else score = minimax(b, depth-1, alpha, beta, false, deadline).score;
      undrop(b, col, r);
      if (score > best.score) best = { score, col };
      alpha = Math.max(alpha, score);
      if (alpha >= beta) break;
    }
    return best;
  } else {
    let best = { score: Infinity, col: ordered[0] };
    for (const col of ordered) {
      const r = dropMut(b, col, HUMAN);
      const win = checkWinAt(b, r, col, HUMAN);
      let score;
      if (win) score = -1000000 - depth;
      else if (!getValidCols(b).length) score = 0;
      else score = minimax(b, depth-1, alpha, beta, true, deadline).score;
      undrop(b, col, r);
      if (score < best.score) best = { score, col };
      beta = Math.min(beta, score);
      if (alpha >= beta) break;
    }
    return best;
  }
};

const iterativeDeepen = (b, maxDepth, timeMs) => {
  const deadline = performance.now() + timeMs;
  const fallback = COL_ORDER.find(c => b[idx(0, c)] === EMPTY) ?? 3;
  let bestCol = fallback;
  for (let d = 1; d <= maxDepth; d++) {
    try {
      const result = minimax(b, d, -Infinity, Infinity, true, deadline);
      if (result.col !== undefined) bestCol = result.col;
      if (Math.abs(result.score) >= 900000) break;
    } catch (e) {
      if (e instanceof TimeUp) break;
      throw e;
    }
  }
  return bestCol;
};

const pickWeightedRandom = (cols) => {
  const weights = cols.map(c => 4 - Math.abs(c - 3));
  const total = weights.reduce((a, w) => a + w, 0);
  let r = Math.random() * total;
  for (let i = 0; i < cols.length; i++) {
    r -= weights[i];
    if (r <= 0) return cols[i];
  }
  return cols[cols.length - 1];
};

const getBotMove = (board, difficulty, overrideTimeMs) => {
  const cfg = DIFFICULTIES[difficulty];
  const b = cloneBoard(board);
  const valid = COL_ORDER.filter(c => b[idx(0, c)] === EMPTY);

  for (const c of valid) {
    const r = dropMut(b, c, BOT);
    const w = checkWinAt(b, r, c, BOT);
    undrop(b, c, r);
    if (w) return c;
  }
  if (Math.random() < cfg.blockChance) {
    for (const c of valid) {
      const r = dropMut(b, c, HUMAN);
      const w = checkWinAt(b, r, c, HUMAN);
      undrop(b, c, r);
      if (w) return c;
    }
  }
  if (cfg.randomChance > 0 && Math.random() < cfg.randomChance) {
    return pickWeightedRandom(valid);
  }

  nodeCount = 0;
  const timeMs = overrideTimeMs ? Math.min(cfg.timeMs, overrideTimeMs) : cfg.timeMs;
  return iterativeDeepen(b, cfg.maxDepth, timeMs);
};

const formatTime = (totalSeconds) => {
  const m = Math.floor(totalSeconds / 60).toString().padStart(2, "0");
  const s = Math.floor(totalSeconds % 60).toString().padStart(2, "0");
  return `${m}:${s}`;
};

const isWin  = (r) => typeof r === "object" && r !== null;
const isDraw = (r) => r === "draw";

const RING_R = 17;
const RING_C = 2 * Math.PI * RING_R;

function TimerRing({ fraction, color, active }) {
  const clamped = Math.max(0, Math.min(1, fraction));
  return (
    <svg width="40" height="40" viewBox="0 0 40 40" style={{ transform: "rotate(-90deg)", flexShrink: 0 }}>
      <circle cx="20" cy="20" r={RING_R} fill="none" stroke="rgba(255,255,255,0.10)" strokeWidth="3" />
      {active && (
        <circle
          cx="20" cy="20" r={RING_R} fill="none" stroke={color} strokeWidth="3" strokeLinecap="round"
          strokeDasharray={RING_C} strokeDashoffset={RING_C * (1 - clamped)}
          style={{ transition: "stroke-dashoffset 0.1s linear, stroke 0.2s" }}
        />
      )}
    </svg>
  );
}

export default function Connect4() {
  const [startingPlayer, setStartingPlayer] = useState(HUMAN);
  const [difficulty, setDifficulty] = useState("Impossible");
  const [humanLimit, setHumanLimit] = useState(null);
  const [botLimit, setBotLimit] = useState(null);
  const [board,     setBoard]     = useState(() => createBoard());
  const [turn,      setTurn]      = useState(startingPlayer);
  const [result,    setResult]    = useState(null);
  const [hoverCol,  setHoverCol]  = useState(null);
  const [thinking,  setThinking]  = useState(false);
  const [lastMove,  setLastMove]  = useState(null);
  const [score,     setScore]     = useState({ you: 0, bot: 0 });
  const [moveCount, setMoveCount] = useState(0);
  const [humanSeconds, setHumanSeconds] = useState(0);
  const [botSeconds,   setBotSeconds]   = useState(0);
  const [moveMsLeft, setMoveMsLeft] = useState(null);
  const [moveEpoch, setMoveEpoch] = useState(0);
  const pendingBot = useRef(false);
  const gameId = useRef(0);
  const boardRef = useRef(board);
  useEffect(() => { boardRef.current = board; }, [board]);

  const tryFinalize = (b, row, col, player) => {
    const winCells = checkWinAt(b, row, col, player);
    if (winCells) {
      setResult({ winner: player, cells: winCells });
      setScore(s => player === HUMAN ? { ...s, you: s.you+1 } : { ...s, bot: s.bot+1 });
      return true;
    }
    if (!getValidCols(b).length) { setResult("draw"); return true; }
    return false;
  };

  const handleDrop = useCallback((col) => {
    if (turn !== HUMAN || result || thinking) return;
    if (board[idx(0, col)] !== EMPTY) return;
    const b = cloneBoard(board);
    const row = dropMut(b, col, HUMAN);
    setBoard(b);
    setLastMove({ row, col, player: HUMAN });
    setMoveCount(n => n + 1);
    setMoveEpoch(n => n + 1);
    if (!tryFinalize(b, row, col, HUMAN)) setTurn(BOT);
  }, [board, turn, result, thinking]);

  useEffect(() => {
    if (turn !== BOT || result || pendingBot.current) return;
    pendingBot.current = true;
    setThinking(true);
    const myGameId = gameId.current;

    setTimeout(() => {
      if (myGameId !== gameId.current) return;

      const snap = cloneBoard(board);
      const overrideMs = botLimit ? Math.max(200, botLimit * 1000 - 200) : undefined;
      const col = getBotMove(snap, difficulty, overrideMs);

      if (myGameId !== gameId.current) return;

      const b    = cloneBoard(snap);
      const row  = dropMut(b, col, BOT);
      setBoard(b);
      setLastMove({ row, col, player: BOT });
      setMoveCount(n => n + 1);
      setMoveEpoch(n => n + 1);
      setThinking(false);
      pendingBot.current = false;
      if (!tryFinalize(b, row, col, BOT)) setTurn(HUMAN);
    }, 60);
  }, [turn, result, difficulty, botLimit]);

  // Cumulative elapsed time per side (chess-clock style, counts up).
  useEffect(() => {
    if (result) return;
    const iv = setInterval(() => {
      if (turn === HUMAN) setHumanSeconds(s => s + 1);
      else setBotSeconds(s => s + 1);
    }, 1000);
    return () => clearInterval(iv);
  }, [turn, result]);

  // Per-move countdown. Resets whenever a new move actually begins. If the
  // human's clock runs out, a move is auto-played so the game can't stall.
  useEffect(() => {
    if (result) { setMoveMsLeft(null); return; }
    const limit = turn === HUMAN ? humanLimit : botLimit;
    if (!limit) { setMoveMsLeft(null); return; }
    const deadline = performance.now() + limit * 1000;
    setMoveMsLeft(limit * 1000);
    const iv = setInterval(() => {
      const remain = deadline - performance.now();
      if (remain <= 0) {
        setMoveMsLeft(0);
        clearInterval(iv);
        if (turn === HUMAN && !thinking) {
          const valid = getValidCols(boardRef.current);
          if (valid.length) handleDrop(pickWeightedRandom(valid));
        }
      } else {
        setMoveMsLeft(remain);
      }
    }, 100);
    return () => clearInterval(iv);
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [turn, result, humanLimit, botLimit, moveEpoch]);

  const startNewGame = (firstPlayer) => {
    gameId.current += 1;
    pendingBot.current = false;
    setBoard(createBoard());
    setTurn(firstPlayer);
    setResult(null);
    setHoverCol(null);
    setThinking(false);
    setLastMove(null);
    setMoveCount(0);
    setHumanSeconds(0);
    setBotSeconds(0);
    setMoveMsLeft(null);
    setMoveEpoch(n => n + 1);
  };

  const reset = () => startNewGame(startingPlayer);
  const chooseStartingPlayer = (player) => { setStartingPlayer(player); startNewGame(player); };

  const winSet = new Set(isWin(result) ? result.cells.map(([r,c]) => `${r},${c}`) : []);

  const BLUE = "#0a84ff", RED = "#ff453a", GREEN = "#30d158", AMBER = "#ff9f0a", PURPLE = "#bf5af2";

  const accentColor =
    isWin(result) && result.winner === HUMAN ? GREEN :
    isWin(result) && result.winner === BOT   ? RED :
    isDraw(result)                           ? AMBER :
    thinking                                 ? PURPLE : BLUE;

  const statusMsg = () => {
    if (isDraw(result))                           return "Draw";
    if (isWin(result) && result.winner === HUMAN) return "You win";
    if (isWin(result) && result.winner === BOT)   return "Bot wins";
    if (thinking)                                 return "Bot is thinking";
    return "Your move";
  };

  const overlayColor = isDraw(result) ? AMBER : isWin(result) && result.winner === HUMAN ? GREEN : RED;
  const overlayLabel = isDraw(result) ? "Draw" : isWin(result) && result.winner === HUMAN ? "You win" : "Bot wins";
  const overlaySub   = isDraw(result) ? "The board filled up with no line of four." :
                        isWin(result) && result.winner === HUMAN ? "Four in a row — nicely played." :
                        "Four in a row for the bot. Run it back?";

  const humanFraction = humanLimit ? (moveMsLeft ?? humanLimit*1000) / (humanLimit*1000) : 1;
  const botFraction   = botLimit   ? (moveMsLeft ?? botLimit*1000)   / (botLimit*1000)   : 1;
  const humanCritical = turn===HUMAN && humanLimit && humanFraction < 0.25;
  const botCritical   = turn===BOT   && botLimit   && botFraction   < 0.25;

  const segBtn = (active, color) => ({
    padding: "7px 14px", fontSize: 13, fontWeight: 600, letterSpacing: "-0.01em",
    borderRadius: 10, cursor: "pointer", border: "none",
    background: active ? color : "transparent",
    color: active ? "#000" : "rgba(255,255,255,0.55)",
    transition: "all 0.15s ease",
  });

  return (
    <div style={{
      position: "fixed", inset: 0, overflow: "hidden",
      background: "radial-gradient(ellipse 120% 90% at 50% -10%, #16161a 0%, #000 55%)",
      display: "flex", flexDirection: "column", alignItems: "center",
      fontFamily: "-apple-system, BlinkMacSystemFont, 'SF Pro Display', 'Inter', 'Segoe UI', Roboto, Helvetica, Arial, sans-serif",
      color: "#f5f5f7", boxSizing: "border-box", userSelect: "none",
    }}>
      <style>{`
        @import url('https://fonts.googleapis.com/css2?family=Inter:wght@400;500;600;700;800;900&display=swap');
        * { box-sizing: border-box; -webkit-tap-highlight-color: transparent; }
        ::-webkit-scrollbar { display: none; }
        @keyframes dropIn   { from{ transform: scale(.3) translateY(-14px); opacity:0 } to{ transform: scale(1) translateY(0); opacity:1 } }
        @keyframes winPulse { from{ transform: scale(.9); filter: brightness(.95) } to{ transform: scale(1.08); filter: brightness(1.35) } }
        @keyframes cardIn   { from{ opacity:0; transform: scale(.92) translateY(10px) } to{ opacity:1; transform: scale(1) translateY(0) } }
        @keyframes dotPulse { 0%,100%{ opacity:.25; transform: scale(.7) } 50%{ opacity:1; transform: scale(1.15) } }
        @keyframes orbDrift { from{ transform: translate(-6%,-4%) scale(1) } to{ transform: translate(6%,4%) scale(1.15) } }
        button:focus-visible, [role="button"]:focus-visible { outline: 2px solid #0a84ff; outline-offset: 2px; }
      `}</style>

      {/* Ambient glow — the one accent flourish, tied to whose turn it is */}
      <div style={{
        position: "absolute", top: "-10%", left: "50%", width: "70vw", maxWidth: 900, height: "50vh",
        transform: "translateX(-50%)", background: `radial-gradient(ellipse, ${accentColor}22 0%, transparent 70%)`,
        filter: "blur(60px)", animation: "orbDrift 14s ease-in-out infinite alternate",
        transition: "background 0.6s ease", pointerEvents: "none", zIndex: 0,
      }} />

      {/* Header */}
      <div style={{ position: "relative", zIndex: 1, textAlign: "center", padding: "clamp(14px,2.5vh,26px) 16px 6px" }}>
        <div style={{ fontSize: "clamp(22px,3.6vw,32px)", fontWeight: 800, letterSpacing: "-0.03em" }}>
          Connect Four
        </div>
        <div style={{ fontSize: 12, color: "rgba(255,255,255,0.4)", marginTop: 2, letterSpacing: "-0.01em" }}>
          Alpha‑beta search · iterative deepening
        </div>
      </div>

      {/* Controls */}
      <div style={{
        position: "relative", zIndex: 1, display: "flex", flexWrap: "wrap", gap: 8, justifyContent: "center",
        padding: "6px 16px", maxWidth: 720,
      }}>
        <div style={{ display: "flex", gap: 2, background: "rgba(255,255,255,0.06)", padding: 3, borderRadius: 13, backdropFilter: "blur(20px)" }}>
          {DIFFICULTY_ORDER.map(level => (
            <button key={level} disabled={thinking} onClick={() => setDifficulty(level)}
              style={segBtn(level === difficulty, level === "Impossible" ? RED : BLUE)}>
              {level}
            </button>
          ))}
        </div>
        <div style={{ display: "flex", gap: 2, background: "rgba(255,255,255,0.06)", padding: 3, borderRadius: 13, backdropFilter: "blur(20px)" }}>
          {[[HUMAN,"You first"],[BOT,"Bot first"]].map(([p,label]) => (
            <button key={label} disabled={thinking} onClick={() => chooseStartingPlayer(p)}
              style={segBtn(startingPlayer === p, "#fff")}>
              {label}
            </button>
          ))}
        </div>
      </div>

      {/* Move-timer settings */}
      <div style={{
        position: "relative", zIndex: 1, display: "flex", gap: 18, flexWrap: "wrap", justifyContent: "center",
        padding: "8px 16px 4px", fontSize: 11,
      }}>
        <div style={{ display: "flex", alignItems: "center", gap: 8 }}>
          <span style={{ color: "rgba(255,255,255,0.4)", fontWeight: 600, letterSpacing: "0.02em" }}>Your clock</span>
          <div style={{ display: "flex", gap: 2, background: "rgba(255,255,255,0.06)", padding: 3, borderRadius: 11 }}>
            {MOVE_LIMIT_OPTIONS.map(opt => (
              <button key={opt.label} onClick={() => setHumanLimit(opt.value)}
                style={{ ...segBtn(humanLimit === opt.value, BLUE), padding: "5px 10px", fontSize: 11 }}>
                {opt.label}
              </button>
            ))}
          </div>
        </div>
        <div style={{ display: "flex", alignItems: "center", gap: 8 }}>
          <span style={{ color: "rgba(255,255,255,0.4)", fontWeight: 600, letterSpacing: "0.02em" }}>Bot's clock</span>
          <div style={{ display: "flex", gap: 2, background: "rgba(255,255,255,0.06)", padding: 3, borderRadius: 11 }}>
            {MOVE_LIMIT_OPTIONS.map(opt => (
              <button key={opt.label} onClick={() => setBotLimit(opt.value)}
                style={{ ...segBtn(botLimit === opt.value, RED), padding: "5px 10px", fontSize: 11 }}>
                {opt.label}
              </button>
            ))}
          </div>
        </div>
      </div>

      {/* Player chips with countdown rings + status */}
      <div style={{
        position: "relative", zIndex: 1, display: "flex", alignItems: "center", gap: 14,
        margin: "10px 0 8px", flexWrap: "wrap", justifyContent: "center", padding: "0 16px",
      }}>
        <div style={{
          display: "flex", alignItems: "center", gap: 8, padding: "6px 12px 6px 6px", borderRadius: 30,
          background: turn===HUMAN && !result ? "rgba(10,132,255,0.14)" : "rgba(255,255,255,0.05)",
          border: `1px solid ${turn===HUMAN && !result ? "rgba(10,132,255,0.4)" : "rgba(255,255,255,0.08)"}`,
          transition: "all 0.2s",
        }}>
          <div style={{ position: "relative", width: 40, height: 40 }}>
            <TimerRing fraction={humanFraction} color={humanCritical ? AMBER : BLUE} active={!!(turn===HUMAN && humanLimit && !result)} />
            <div style={{ position: "absolute", inset: 0, display: "flex", alignItems: "center", justifyContent: "center", fontSize: 15 }}>🔵</div>
          </div>
          <div>
            <div style={{ fontSize: 13, fontWeight: 700 }}>You · {score.you}</div>
            <div style={{ fontSize: 11, color: "rgba(255,255,255,0.4)" }}>
              {turn===HUMAN && humanLimit && !result ? `${Math.ceil((moveMsLeft ?? 0)/1000)}s left` : formatTime(humanSeconds)}
            </div>
          </div>
        </div>

        <div style={{
          padding: "7px 16px", borderRadius: 20, fontSize: 13, fontWeight: 600, letterSpacing: "-0.01em",
          background: `${accentColor}1a`, border: `1px solid ${accentColor}40`, color: accentColor,
          display: "flex", alignItems: "center", gap: 7, transition: "all 0.3s",
        }}>
          {thinking && [0,1,2].map(i => (
            <span key={i} style={{ width: 4, height: 4, borderRadius: "50%", background: PURPLE, animation: `dotPulse 0.9s ${i*0.2}s infinite` }} />
          ))}
          {statusMsg()}
        </div>

        <div style={{
          display: "flex", alignItems: "center", gap: 8, padding: "6px 6px 6px 12px", borderRadius: 30,
          background: turn===BOT && !result ? "rgba(255,69,58,0.14)" : "rgba(255,255,255,0.05)",
          border: `1px solid ${turn===BOT && !result ? "rgba(255,69,58,0.4)" : "rgba(255,255,255,0.08)"}`,
          transition: "all 0.2s", flexDirection: "row-reverse",
        }}>
          <div style={{ position: "relative", width: 40, height: 40 }}>
            <TimerRing fraction={botFraction} color={botCritical ? AMBER : RED} active={!!(turn===BOT && botLimit && !result)} />
            <div style={{ position: "absolute", inset: 0, display: "flex", alignItems: "center", justifyContent: "center", fontSize: 15 }}>🔴</div>
          </div>
          <div style={{ textAlign: "right" }}>
            <div style={{ fontSize: 13, fontWeight: 700 }}>Bot · {score.bot}</div>
            <div style={{ fontSize: 11, color: "rgba(255,255,255,0.4)" }}>
              {turn===BOT && botLimit && !result ? `${Math.ceil((moveMsLeft ?? 0)/1000)}s left` : formatTime(botSeconds)}
            </div>
          </div>
        </div>
      </div>

      {/* Board */}
      <div style={{
        position: "relative", zIndex: 1, flex: 1, display: "flex", flexDirection: "column",
        alignItems: "center", justifyContent: "center", width: "100%", minHeight: 0, padding: "4px 10px",
        "--cell": "min(52px, 11.5vw, 9.5vh)",
      }}>
        <div style={{ display: "flex", gap: "calc(var(--cell) * 0.1)", marginBottom: 4, paddingInline: "calc(var(--cell) * 0.19)" }}>
          {Array.from({ length: COLS }, (_,c) => {
            const active = hoverCol===c && turn===HUMAN && !result && !thinking;
            const full   = board[idx(0,c)] !== EMPTY;
            return (
              <div key={c} style={{ width: "var(--cell)", height: 14, display: "flex", alignItems: "center", justifyContent: "center" }}>
                {active && !full && (
                  <div style={{ width: 0, height: 0, borderLeft: "6px solid transparent", borderRight: "6px solid transparent",
                    borderTop: `9px solid ${accentColor}`, filter: `drop-shadow(0 0 4px ${accentColor})` }} />
                )}
                {active && full && <span style={{ color: RED, fontSize: 12 }}>✕</span>}
              </div>
            );
          })}
        </div>

        <div style={{
          background: "linear-gradient(165deg, rgba(255,255,255,0.07), rgba(255,255,255,0.02))",
          borderRadius: 24, padding: "calc(var(--cell) * 0.19)",
          border: "1px solid rgba(255,255,255,0.08)",
          boxShadow: `0 30px 70px rgba(0,0,0,0.55), inset 0 1px 0 rgba(255,255,255,0.06), 0 0 46px ${accentColor}1a`,
          backdropFilter: "blur(18px)", transition: "box-shadow 0.5s",
        }}>
          {Array.from({ length: ROWS }, (_,r) => (
            <div key={r} style={{ display: "flex", gap: "calc(var(--cell) * 0.1)", marginBottom: r<ROWS-1 ? "calc(var(--cell) * 0.1)" : 0 }}>
              {Array.from({ length: COLS }, (_,c) => {
                const cell      = board[idx(r,c)];
                const cellIsWin = winSet.has(`${r},${c}`);
                const isLast    = lastMove?.row===r && lastMove?.col===c;
                const hovering  = hoverCol===c && !result && !thinking && turn===HUMAN && cell===EMPTY;
                const colFull   = board[idx(0,c)] !== EMPTY;
                let fill = "transparent", glow = "transparent";
                if (cell===HUMAN) { fill = cellIsWin ? `linear-gradient(150deg, #7ee0a8, ${GREEN})` : `linear-gradient(150deg, #6ab8ff, ${BLUE})`; glow = cellIsWin ? GREEN : BLUE; }
                else if (cell===BOT) { fill = cellIsWin ? `linear-gradient(150deg, #ff9a91, #d6392f)` : `linear-gradient(150deg, #ff8079, ${RED})`; glow = cellIsWin ? "#d6392f" : RED; }
                return (
                  <div key={c}
                    onClick={() => handleDrop(c)}
                    onMouseEnter={() => setHoverCol(c)}
                    onMouseLeave={() => setHoverCol(null)}
                    style={{
                      width: "var(--cell)", height: "var(--cell)", borderRadius: "50%",
                      background: hovering ? "rgba(255,255,255,0.10)" : "rgba(0,0,0,0.55)",
                      border: isLast && cell!==EMPTY ? `2px solid ${glow}cc` : hovering ? `2px solid ${accentColor}55` : "2px solid rgba(255,255,255,0.05)",
                      cursor: turn===HUMAN && !result && !thinking && !colFull ? "pointer" : "default",
                      display: "flex", alignItems: "center", justifyContent: "center",
                      transition: "background 0.12s, border-color 0.12s",
                      boxShadow: "inset 0 3px 10px rgba(0,0,0,0.7)", flexShrink: 0,
                    }}
                  >
                    {cell !== EMPTY && (
                      <div style={{
                        width: "calc(var(--cell) - 9px)", height: "calc(var(--cell) - 9px)", borderRadius: "50%", background: fill,
                        boxShadow: cellIsWin
                          ? `0 0 18px ${glow}, 0 0 36px ${glow}55, inset 0 -2px 5px rgba(0,0,0,0.35), inset 0 2px 4px rgba(255,255,255,0.25)`
                          : `0 0 ${isLast?10:3}px ${glow}${isLast?"bb":"33"}, inset 0 -2px 5px rgba(0,0,0,0.3), inset 0 2px 4px rgba(255,255,255,0.2)`,
                        animation: cellIsWin ? "winPulse 0.7s ease-in-out infinite alternate" : isLast ? "dropIn 0.24s cubic-bezier(.34,1.56,.64,1) both" : "none",
                      }} />
                    )}
                  </div>
                );
              })}
            </div>
          ))}
        </div>
      </div>

      {/* Footer */}
      <div style={{ position: "relative", zIndex: 1, display: "flex", alignItems: "center", gap: 14, padding: "10px 16px clamp(14px,3vh,26px)" }}>
        <div style={{ fontSize: 12, color: "rgba(255,255,255,0.35)" }}>{moveCount} moves played</div>
        <button
          onClick={reset}
          style={{
            padding: "9px 22px", borderRadius: 20, border: "1px solid rgba(255,255,255,0.14)",
            background: "rgba(255,255,255,0.07)", color: "#f5f5f7", fontWeight: 600, fontSize: 13,
            cursor: "pointer", letterSpacing: "-0.01em", transition: "background 0.15s",
            fontFamily: "inherit",
          }}
          onMouseEnter={e => { e.currentTarget.style.background = "rgba(255,255,255,0.13)"; }}
          onMouseLeave={e => { e.currentTarget.style.background = "rgba(255,255,255,0.07)"; }}
        >
          New game
        </button>
      </div>

      {/* Game-over card */}
      {result && (
        <div onClick={reset} style={{
          position: "fixed", inset: 0, zIndex: 50, background: "rgba(0,0,0,0.55)", backdropFilter: "blur(14px)",
          display: "flex", alignItems: "center", justifyContent: "center", cursor: "pointer", padding: 20,
        }}>
          <div style={{
            width: "min(360px, 88vw)", borderRadius: 28, padding: "36px 30px 30px",
            background: "linear-gradient(165deg, rgba(40,40,44,0.9), rgba(20,20,23,0.92))",
            border: "1px solid rgba(255,255,255,0.1)", textAlign: "center",
            boxShadow: `0 30px 80px rgba(0,0,0,0.6), 0 0 60px ${overlayColor}22`,
            animation: "cardIn 0.35s cubic-bezier(.34,1.56,.64,1) both",
          }}>
            <div style={{ fontSize: 40, fontWeight: 800, letterSpacing: "-0.03em", color: overlayColor, marginBottom: 8 }}>
              {overlayLabel}
            </div>
            <div style={{ fontSize: 14, color: "rgba(255,255,255,0.55)", marginBottom: 24, lineHeight: 1.4 }}>
              {overlaySub}
            </div>
            <button
              onClick={(e) => { e.stopPropagation(); reset(); }}
              style={{
                padding: "12px 30px", borderRadius: 16, border: "none", background: overlayColor,
                color: "#000", fontWeight: 700, fontSize: 15, cursor: "pointer", fontFamily: "inherit",
              }}
            >
              Play again
            </button>
          </div>
        </div>
      )}
    </div>
  );
}
