
import { useState, useEffect, useCallback, useRef } from "react";

const ROWS = 6;
const COLS = 7;
const EMPTY = 0;
const HUMAN = 1;
const BOT = 2;

type Board = number[];
type GameResult = { winner: number; cells: [number, number][] } | "draw" | "timeout_human" | "timeout_bot" | null;
type LastMove = { row: number; col: number; player: number } | null;
type DifficultyLevel = "Easy" | "Medium" | "Hard" | "Impossible";

const DIFFICULTIES: Record<DifficultyLevel, { maxDepth: number; timeMs: number; blockChance: number; randomChance: number }> = {
  Easy:       { maxDepth: 2,  timeMs: 100,  blockChance: 0.45, randomChance: 0.40 },
  Medium:     { maxDepth: 4,  timeMs: 250,  blockChance: 0.80, randomChance: 0.15 },
  Hard:       { maxDepth: 7,  timeMs: 500,  blockChance: 1.00, randomChance: 0.02 },
  Impossible: { maxDepth: 22, timeMs: 2000, blockChance: 1.00, randomChance: 0 },
};
const DIFFICULTY_ORDER: DifficultyLevel[] = ["Easy", "Medium", "Hard", "Impossible"];
const TIMER_OPTIONS = [5, 10, 15, 0]; // 0 = unlimited

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
  if(bot===3&&hum===0) return 120;
  if(bot===2&&hum===0) return 16;
  if(hum===3&&bot===0) return -300;
  if(hum===2&&bot===0) return -25;
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
const transpositionTable = new Map<string, { depth: number; score: number; col: number }>();

const getBoardHash = (b: Board): string => b.join('');

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

  const boardHash = getBoardHash(b);
  const ttEntry = transpositionTable.get(boardHash);
  if (ttEntry && ttEntry.depth >= depth) {
    return { score: ttEntry.score, col: ttEntry.col };
  }

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

  let bestCol = ordered[0];

  if (maximizing) {
    let best = { score: -Infinity, col: bestCol };
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
    transpositionTable.set(boardHash, { depth, score: best.score, col: best.col });
    return best;
  } else {
    let best = { score: Infinity, col: bestCol };
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
    transpositionTable.set(boardHash, { depth, score: best.score, col: best.col });
    return best;
  }
};

const iterativeDeepen = (b: Board, maxDepth: number, timeMs: number): number => {
  const deadline = performance.now() + timeMs;
  const fallback = COL_ORDER.find(c => b[idx(0, c)] === EMPTY) ?? 3;
  let bestCol = fallback;
  transpositionTable.clear();

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

const getBotMove = (board: Board, difficulty: DifficultyLevel): number => {
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
  return iterativeDeepen(b, cfg.maxDepth, cfg.timeMs);
};

const isWin  = (r: GameResult): r is { winner: number; cells: [number,number][] } => typeof r === "object" && r !== null;
const isDraw = (r: GameResult): r is "draw" => r === "draw";

export default function Connect4() {
  const [startingPlayer, setStartingPlayer] = useState<number>(HUMAN);
  const [difficulty, setDifficulty] = useState<DifficultyLevel>("Impossible");
  const [turnLimit, setTurnLimit] = useState<number>(10);
  const [timeLeft, setTimeLeft] = useState<number>(10);
  const [board, setBoard] = useState<Board>(() => createBoard());
  const [turn, setTurn] = useState<number>(startingPlayer);
  const [result, setResult] = useState<GameResult>(null);
  const [hoverCol, setHoverCol] = useState<number | null>(null);
  const [thinking, setThinking] = useState(false);
  const [lastMove, setLastMove] = useState<LastMove>(null);
  const [score, setScore] = useState({ you: 0, bot: 0 });
  const [moveCount, setMoveCount] = useState(0);

  const pendingBot = useRef(false);
  const gameId = useRef(0);

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
    setTimeLeft(turnLimit);
    if (!tryFinalize(b, row, col, HUMAN)) setTurn(BOT);
  }, [board, turn, result, thinking, turnLimit]);

  useEffect(() => {
    if (turn !== BOT || result || pendingBot.current) return;
    pendingBot.current = true;
    setThinking(true);
    const myGameId = gameId.current;

    setTimeout(() => {
      if (myGameId !== gameId.current) return;

      const snap = cloneBoard(board);
      const col  = getBotMove(snap, difficulty);

      if (myGameId !== gameId.current) return;

      const b    = cloneBoard(snap);
      const row  = dropMut(b, col, BOT);
      setBoard(b);
      setLastMove({ row, col, player: BOT });
      setMoveCount(n => n + 1);
      setThinking(false);
      pendingBot.current = false;
      setTimeLeft(turnLimit);
      if (!tryFinalize(b, row, col, BOT)) setTurn(HUMAN);
    }, 60);
  }, [turn, result, difficulty, turnLimit]);

  useEffect(() => {
    if (result || turnLimit === 0) return;
    const interval = setInterval(() => {
      setTimeLeft(prev => {
        if (prev <= 1) {
          if (turn === HUMAN) {
            setResult("timeout_human");
            setScore(s => ({ ...s, bot: s.bot + 1 }));
          } else {
            setResult("timeout_bot");
            setScore(s => ({ ...s, you: s.you + 1 }));
          }
          return 0;
        }
        return prev - 1;
      });
    }, 1000);
    return () => clearInterval(interval);
  }, [turn, result, turnLimit]);

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
    setTimeLeft(turnLimit);
  };

  const reset = () => startNewGame(startingPlayer);

  const winSet = new Set(
    isWin(result) ? result.cells.map(([r,c]) => `${r},${c}`) : []
  );

  const accentColor =
    isWin(result) && result.winner === HUMAN ? "#22c55e" :
    (isWin(result) && result.winner === BOT) || result === "timeout_human" ? "#ef4444" :
    isDraw(result)                           ? "#f59e0b" :
    thinking                                 ? "#a855f7" : "#3b82f6";

  const statusMsg = (): string => {
    if (result === "timeout_human") return "TIME EXPIRED! BOT WINS 💀";
    if (result === "timeout_bot")   return "BOT TIMED OUT! YOU WIN 🎉";
    if (isDraw(result))             return "DRAW";
    if (isWin(result) && result.winner === HUMAN) return "YOU WIN! 🎉";
    if (isWin(result) && result.winner === BOT)   return "UNBEATABLE BOT VICTORIOUS 💀";
    if (thinking) return "BOT IS COMPUTING...";
    return "YOUR TURN";
  };

  const cellSize = typeof window !== "undefined" && window.innerWidth < 480 ? 42 : 52;

  return (
    <div style={{ minHeight:"100vh", width:"100%", background:"linear-gradient(135deg,#0a0015 0%,#06001a 40%,#100010 70%,#1a0005 100%)", display:"flex", flexDirection:"column", alignItems:"center", justifyContent:"center", fontFamily:"'Courier New',monospace", padding:"12px 8px", userSelect:"none", position:"relative", boxSizing:"border-box" }}>

      <div style={{ textAlign:"center", marginBottom:"10px" }}>
        <div style={{ fontSize:"clamp(20px,6vw,42px)", fontWeight:900, letterSpacing:"0.2em", background:"linear-gradient(135deg,#ff6b6b 0%,#c084fc 45%,#60a5fa 100%)", WebkitBackgroundClip:"text", WebkitTextFillColor:"transparent" }}>CONNECT FOUR</div>
        <div style={{ color:"#4a3060", fontSize:"9px", letterSpacing:"0.35em" }}>PERFECT AI SOLVER + MATCH TIMER</div>
      </div>

      <div style={{ display:"flex", gap:"6px", marginBottom:"8px" }}>
        {DIFFICULTY_ORDER.map(level => (
          <button
            key={level}
            onClick={() => setDifficulty(level)}
            disabled={thinking}
            style={{
              padding:"4px 10px", fontSize:"10px", borderRadius:"12px",
              border:`1px solid ${level === difficulty ? "#be123c" : "#ffffff14"}`,
              background: level === difficulty ? "#be123c22" : "transparent",
              color: level === difficulty ? "#fda4af" : "#6b6890",
            }}
          >
            {level}
          </button>
        ))}
      </div>

      <div style={{ display:"flex", alignItems:"center", gap:"8px", marginBottom:"8px" }}>
        <span style={{ fontSize:"9px", color:"#a5b4fc" }}>MOVE TIMER:</span>
        {TIMER_OPTIONS.map(sec => (
          <button
            key={sec}
            onClick={() => { setTurnLimit(sec); setTimeLeft(sec); }}
            style={{
              padding:"3px 8px", fontSize:"10px", borderRadius:"10px",
              border: `1px solid ${turnLimit === sec ? "#38bdf8" : "#ffffff14"}`,
              background: turnLimit === sec ? "#38bdf822" : "transparent",
              color: turnLimit === sec ? "#7dd3fc" : "#6b6890"
            }}
          >
            {sec === 0 ? "Off" : `${sec}s`}
          </button>
        ))}
      </div>

      {turnLimit > 0 && !result && (
        <div style={{ color: timeLeft <= 3 ? "#ef4444" : "#f59e0b", fontSize:"14px", fontWeight:"bold", marginBottom:"8px" }}>
          ⏱ TIME REMAINING: {timeLeft}s
        </div>
      )}

      <div style={{ display:"flex", marginBottom:"10px", border:"1px solid #ffffff0f", borderRadius:"6px", background:"rgba(0,0,0,0.35)" }}>
        <div style={{ padding:"6px 16px", textAlign:"center" }}>
          <div style={{ color:"#ffffff33", fontSize:"8px" }}>YOU</div>
          <div style={{ color:"#60a5fa", fontSize:"14px", fontWeight:900 }}>{score.you}</div>
        </div>
        <div style={{ padding:"6px 16px", textAlign:"center", borderLeft:"1px solid #ffffff0a", borderRight:"1px solid #ffffff0a" }}>
          <div style={{ color:"#ffffff33", fontSize:"8px" }}>MOVES</div>
          <div style={{ color:"#a78bfa", fontSize:"14px", fontWeight:900 }}>{moveCount}</div>
        </div>
        <div style={{ padding:"6px 16px", textAlign:"center" }}>
          <div style={{ color:"#ffffff33", fontSize:"8px" }}>BOT</div>
          <div style={{ color:"#f87171", fontSize:"14px", fontWeight:900 }}>{score.bot}</div>
        </div>
      </div>

      <div style={{ marginBottom:"10px", padding:"6px 16px", border:`1px solid ${accentColor}44`, background:`${accentColor}12`, color:accentColor, fontSize:"11px", fontWeight:700, borderRadius:"16px" }}>
        {statusMsg()}
      </div>

      <div style={{ background:"#08062a", borderRadius:"12px", padding:"8px", border:"1px solid #ffffff0d" }}>
        {Array.from({ length:ROWS }, (_,r) => (
          <div key={r} style={{ display:"flex", gap:"5px", marginBottom:r<ROWS-1?"5px":0 }}>
            {Array.from({ length:COLS }, (_,c) => {
              const cell = board[idx(r,c)];
              const cellIsWin = winSet.has(`${r},${c}`);
              let fill = "transparent";
              if (cell===HUMAN) fill = cellIsWin ? "#22c55e" : "#3b82f6";
              else if (cell===BOT) fill = cellIsWin ? "#ef4444" : "#be123c";

              return (
                <div key={c}
                  onClick={() => handleDrop(c)}
                  onMouseEnter={() => setHoverCol(c)}
                  style={{ width:`${cellSize}px`, height:`${cellSize}px`, borderRadius:"50%", background:hoverCol===c?"#1c1950":"#06041a", border:"1px solid #ffffff11", cursor:"pointer", display:"flex", alignItems:"center", justifyContent:"center" }}
                >
                  {cell !== EMPTY && (
                    <div style={{ width:`${cellSize-10}px`, height:`${cellSize-10}px`, borderRadius:"50%", background:fill }} />
                  )}
                </div>
              );
            })}
          </div>
        ))}
      </div>

      <button onClick={reset} style={{ marginTop:"14px", padding:"6px 20px", background:"transparent", border:"1px solid #6366f1", color:"#818cf8", borderRadius:"16px", cursor:"pointer", fontSize:"11px" }}>
        ↺ RESET GAME
      </button>
    </div>
  );
}
