import { useState, useEffect, useCallback, useRef } from "react";
import type { CSSProperties } from "react";
import "./assets/Connect4.css";

const ROWS = 6;
const COLS = 7;
const EMPTY = 0;
const HUMAN = 1;
const BOT = 2;

type Board = number[];
type GameResult = { winner: number; cells: [number, number][] } | "draw" | null;
type LastMove = { row: number; col: number; player: number } | null;
type DifficultyLevel = "Easy" | "Medium" | "Hard" | "Impossible";
type MoveLimit = number | null;

// ── Difficulty configuration ────────────────────────────────────────────────
// Easy/Medium can blunder or skip blocks on purpose. Hard rarely does.
// "Impossible" never blunders and always takes an immediate win/block, then
// searches as deep as the time budget allows. NOTE: this is a strong
// heuristic alpha-beta search, not a fully solved Connect Four oracle (that
// requires reasoning about all ~4.5 trillion positions / up to 42-ply
// lines). It plays extremely well but is not mathematically unbeatable.
const DIFFICULTIES: Record<DifficultyLevel, { maxDepth: number; timeMs: number; blockChance: number; randomChance: number }> = {
  Easy:       { maxDepth: 2,  timeMs: 150,  blockChance: 0.45, randomChance: 0.40 },
  Medium:     { maxDepth: 4,  timeMs: 300,  blockChance: 0.80, randomChance: 0.15 },
  Hard:       { maxDepth: 7,  timeMs: 700,  blockChance: 1.00, randomChance: 0.03 },
  Impossible: { maxDepth: 15, timeMs: 2200, blockChance: 1.00, randomChance: 0 },
};
const DIFFICULTY_ORDER: DifficultyLevel[] = ["Easy", "Medium", "Hard", "Impossible"];
const MOVE_LIMIT_OPTIONS: { label: string; value: MoveLimit }[] = [
  { label: "Off", value: null },
  { label: "10s", value: 10 },
  { label: "20s", value: 20 },
  { label: "30s", value: 30 },
];

const idx = (r: number, c: number) => r * COLS + c;
const createBoard = (): Board => new Array(ROWS * COLS).fill(EMPTY);
const cloneBoard = (b: Board): Board => [...b];

const getRow = (b: Board, col: number): number => {
  for (let r = ROWS - 1; r >= 0; r--) if (b[idx(r, col)] === EMPTY) return r;
  return -1;
};
const getValidCols = (b: Board): number[] => {
  const cols: number[] = [];
  for (let c = 0; c < COLS; c++) if (b[idx(0, c)] === EMPTY) cols.push(c);
  return cols;
};
const dropMut = (b: Board, col: number, player: number): number => {
  const r = getRow(b, col);
  if (r === -1) return -1;
  b[idx(r, col)] = player;
  return r;
};
const undrop = (b: Board, col: number, row: number): void => { b[idx(row, col)] = EMPTY; };

const checkWinAt = (b: Board, row: number, col: number, player: number): [number, number][] | null => {
  const dirs: [number, number][] = [[0,1],[1,0],[1,1],[1,-1]];
  for (const [dr, dc] of dirs) {
    let count = 1;
    const cells: [number, number][] = [[row, col]];
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

const scoreWindow4 = (a: number, b: number, c: number, d: number): number => {
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

const staticScore = (b: Board): number => {
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

const minimax = (
  b: Board,
  depth: number,
  alpha: number,
  beta: number,
  maximizing: boolean,
  deadline?: number
): { score: number; col?: number } => {
  nodeCount++;
  if (deadline && (nodeCount & 511) === 0 && performance.now() > deadline) throw new TimeUp();

  const valid = COL_ORDER.filter(c => b[idx(0,c)] === EMPTY);
  if (!valid.length) return { score: 0 };
  if (depth === 0) return { score: staticScore(b) };
  const player = maximizing ? BOT : HUMAN;
  const opp    = maximizing ? HUMAN : BOT;
  const wins: number[] = [], blocks: number[] = [], rest: number[] = [];
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
      let score: number;
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
      let score: number;
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

const iterativeDeepen = (b: Board, maxDepth: number, timeMs: number): number => {
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

const pickWeightedRandom = (cols: number[]): number => {
  const weights = cols.map(c => 4 - Math.abs(c - 3));
  const total = weights.reduce((a, w) => a + w, 0);
  let r = Math.random() * total;
  for (let i = 0; i < cols.length; i++) {
    r -= weights[i];
    if (r <= 0) return cols[i];
  }
  return cols[cols.length - 1];
};

const getBotMove = (board: Board, difficulty: DifficultyLevel, overrideTimeMs?: number): number => {
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

const formatTime = (totalSeconds: number): string => {
  const m = Math.floor(totalSeconds / 60).toString().padStart(2, "0");
  const s = Math.floor(totalSeconds % 60).toString().padStart(2, "0");
  return `${m}:${s}`;
};

const isWin  = (r: GameResult): r is { winner: number; cells: [number,number][] } => typeof r === "object" && r !== null;
const isDraw = (r: GameResult): r is "draw" => r === "draw";

const RING_R = 17;
const RING_C = 2 * Math.PI * RING_R;

function TimerRing({ fraction, color, active }: { fraction: number; color: string; active: boolean }) {
  const clamped = Math.max(0, Math.min(1, fraction));
  return (
    <svg className="c4-ring-svg" width="40" height="40" viewBox="0 0 40 40">
      <circle className="c4-ring-track" cx="20" cy="20" r={RING_R} />
      {active && (
        <circle
          className="c4-ring-fill"
          cx="20" cy="20" r={RING_R}
          stroke={color}
          strokeDasharray={RING_C}
          strokeDashoffset={RING_C * (1 - clamped)}
        />
      )}
    </svg>
  );
}

const BLUE = "#0a84ff", RED = "#ff453a", GREEN = "#30d158", AMBER = "#ff9f0a", PURPLE = "#bf5af2";

export default function Connect4() {
  const [startingPlayer, setStartingPlayer] = useState<number>(HUMAN);
  const [difficulty, setDifficulty] = useState<DifficultyLevel>("Impossible");
  const [humanLimit, setHumanLimit] = useState<MoveLimit>(null);
  const [botLimit, setBotLimit] = useState<MoveLimit>(null);
  const [board,     setBoard]     = useState<Board>(() => createBoard());
  const [turn,      setTurn]      = useState<number>(startingPlayer);
  const [result,    setResult]    = useState<GameResult>(null);
  const [hoverCol,  setHoverCol]  = useState<number | null>(null);
  const [thinking,  setThinking]  = useState(false);
  const [lastMove,  setLastMove]  = useState<LastMove>(null);
  const [score,     setScore]     = useState({ you: 0, bot: 0 });
  const [moveCount, setMoveCount] = useState(0);
  const [humanSeconds, setHumanSeconds] = useState(0);
  const [botSeconds,   setBotSeconds]   = useState(0);
  const [moveMsLeft, setMoveMsLeft] = useState<number | null>(null);
  const [moveEpoch, setMoveEpoch] = useState(0);
  const pendingBot = useRef(false);
  const gameId = useRef(0);
  const boardRef = useRef(board);
  useEffect(() => { boardRef.current = board; }, [board]);

  const tryFinalize = (b: Board, row: number, col: number, player: number): boolean => {
    const winCells = checkWinAt(b, row, col, player);
    if (winCells) {
      setResult({ winner: player, cells: winCells });
      setScore(s => player === HUMAN ? { ...s, you: s.you+1 } : { ...s, bot: s.bot+1 });
      return true;
    }
    if (!getValidCols(b).length) { setResult("draw"); return true; }
    return false;
  };

  const handleDrop = useCallback((col: number) => {
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

  const startNewGame = (firstPlayer: number) => {
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
  const chooseStartingPlayer = (player: number) => { setStartingPlayer(player); startNewGame(player); };

  const winSet = new Set(isWin(result) ? result.cells.map(([r,c]) => `${r},${c}`) : []);

  const accentColor =
    isWin(result) && result.winner === HUMAN ? GREEN :
    isWin(result) && result.winner === BOT   ? RED :
    isDraw(result)                           ? AMBER :
    thinking                                 ? PURPLE : BLUE;

  const statusMsg = (): string => {
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
  const humanCritical = turn===HUMAN && !!humanLimit && humanFraction < 0.25;
  const botCritical   = turn===BOT   && !!botLimit   && botFraction   < 0.25;

  const segClass = (active: boolean, color: "blue"|"red"|"white", sm = false) =>
    `c4-seg-btn ${sm ? "c4-seg-btn--sm" : ""} ${active ? `c4-seg-btn--active-${color}` : ""}`;

  return (
    <div className="c4-root" style={{ "--accent": accentColor } as CSSProperties}>
      <div className="c4-bg-glow" />

      {/* Header */}
      <div className="c4-header">
        <div className="c4-title">Connect Four</div>
        <div className="c4-subtitle">Alpha‑beta search · iterative deepening</div>
      </div>

      {/* Difficulty / first-move controls */}
      <div className="c4-controls">
        <div className="c4-seg">
          {DIFFICULTY_ORDER.map(level => (
            <button key={level} disabled={thinking} onClick={() => setDifficulty(level)}
              className={segClass(level === difficulty, level === "Impossible" ? "red" : "blue")}>
              {level}
            </button>
          ))}
        </div>
        <div className="c4-seg">
          {([[HUMAN,"You first"],[BOT,"Bot first"]] as [number,string][]).map(([p,label]) => (
            <button key={label} disabled={thinking} onClick={() => chooseStartingPlayer(p)}
              className={segClass(startingPlayer === p, "white")}>
              {label}
            </button>
          ))}
        </div>
      </div>

      {/* Move-timer settings */}
      <div className="c4-timer-row">
        <div className="c4-timer-group">
          <span className="c4-timer-label">Your clock</span>
          <div className="c4-seg c4-seg--sm">
            {MOVE_LIMIT_OPTIONS.map(opt => (
              <button key={opt.label} onClick={() => setHumanLimit(opt.value)}
                className={segClass(humanLimit === opt.value, "blue", true)}>
                {opt.label}
              </button>
            ))}
          </div>
        </div>
        <div className="c4-timer-group">
          <span className="c4-timer-label">Bot's clock</span>
          <div className="c4-seg c4-seg--sm">
            {MOVE_LIMIT_OPTIONS.map(opt => (
              <button key={opt.label} onClick={() => setBotLimit(opt.value)}
                className={segClass(botLimit === opt.value, "red", true)}>
                {opt.label}
              </button>
            ))}
          </div>
        </div>
      </div>

      {/* Player chips + status */}
      <div className="c4-status-row">
        <div className={`c4-chip ${turn===HUMAN && !result ? "c4-chip--active-human" : ""}`}>
          <div className="c4-ring-wrap">
            <TimerRing fraction={humanFraction} color={humanCritical ? AMBER : BLUE} active={!!(turn===HUMAN && humanLimit && !result)} />
            <div className="c4-ring-emoji">🔵</div>
          </div>
          <div>
            <div className="c4-chip-name">You · {score.you}</div>
            <div className="c4-chip-sub">
              {turn===HUMAN && humanLimit && !result ? `${Math.ceil((moveMsLeft ?? 0)/1000)}s left` : formatTime(humanSeconds)}
            </div>
          </div>
        </div>

        <div className="c4-status-pill">
          {thinking && [0,1,2].map(i => (
            <span key={i} className="c4-status-dot" style={{ animationDelay: `${i*0.2}s` }} />
          ))}
          {statusMsg()}
        </div>

        <div className={`c4-chip c4-chip--bot ${turn===BOT && !result ? "c4-chip--active-bot" : ""}`}>
          <div className="c4-ring-wrap">
            <TimerRing fraction={botFraction} color={botCritical ? AMBER : RED} active={!!(turn===BOT && botLimit && !result)} />
            <div className="c4-ring-emoji">🔴</div>
          </div>
          <div className="c4-chip-sub--right">
            <div className="c4-chip-name">Bot · {score.bot}</div>
            <div className="c4-chip-sub">
              {turn===BOT && botLimit && !result ? `${Math.ceil((moveMsLeft ?? 0)/1000)}s left` : formatTime(botSeconds)}
            </div>
          </div>
        </div>
      </div>

      {/* Board */}
      <div className="c4-board-outer">
        <div className="c4-arrow-row">
          {Array.from({ length: COLS }, (_,c) => {
            const active = hoverCol===c && turn===HUMAN && !result && !thinking;
            const full   = board[idx(0,c)] !== EMPTY;
            return (
              <div key={c} className="c4-arrow-cell">
                {active && !full && <div className="c4-arrow-triangle" />}
                {active && full && <span className="c4-arrow-x">✕</span>}
              </div>
            );
          })}
        </div>

        <div className="c4-grid">
          {Array.from({ length: ROWS }, (_,r) => (
            <div key={r} className="c4-row">
              {Array.from({ length: COLS }, (_,c) => {
                const cell      = board[idx(r,c)];
                const cellIsWin = winSet.has(`${r},${c}`);
                const isLast    = lastMove?.row===r && lastMove?.col===c;
                const hovering  = hoverCol===c && !result && !thinking && turn===HUMAN && cell===EMPTY;
                const colFull   = board[idx(0,c)] !== EMPTY;
                const clickable = turn===HUMAN && !result && !thinking && !colFull;

                let pieceClass = "";
                if (cell===HUMAN) pieceClass = cellIsWin ? "c4-piece c4-piece--human-win" : "c4-piece c4-piece--human";
                else if (cell===BOT) pieceClass = cellIsWin ? "c4-piece c4-piece--bot-win" : "c4-piece c4-piece--bot";
                if (isLast && cell!==EMPTY && !cellIsWin) pieceClass += " c4-piece--last";

                return (
                  <div key={c}
                    onClick={() => handleDrop(c)}
                    onMouseEnter={() => setHoverCol(c)}
                    onMouseLeave={() => setHoverCol(null)}
                    className={[
                      "c4-cell",
                      clickable ? "c4-cell--hoverable" : "",
                      hovering ? "c4-cell--hovering" : "",
                      isLast && cell!==EMPTY ? "c4-cell--last-move" : "",
                    ].join(" ")}
                    style={{ "--glow": cell===HUMAN ? (cellIsWin?GREEN:BLUE) : cell===BOT ? (cellIsWin?"#d6392f":RED) : "transparent" } as CSSProperties}
                  >
                    {cell !== EMPTY && <div className={pieceClass} />}
                  </div>
                );
              })}
            </div>
          ))}
        </div>
      </div>

      {/* Footer */}
      <div className="c4-footer">
        <div className="c4-move-count">{moveCount} moves played</div>
        <button className="c4-btn" onClick={reset}>New game</button>
      </div>

      {/* Game-over card */}
      {result && (
        <div className="c4-overlay" onClick={reset} style={{ "--overlay": overlayColor } as CSSProperties}>
          <div className="c4-overlay-card">
            <div className="c4-overlay-title">{overlayLabel}</div>
            <div className="c4-overlay-sub">{overlaySub}</div>
            <button className="c4-overlay-btn" onClick={(e) => { e.stopPropagation(); reset(); }}>
              Play again
            </button>
          </div>
        </div>
      )}
    </div>
  );
}
