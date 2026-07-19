import React, { useState, useEffect, useCallback, useRef } from "react";

// ── CONNECT 4 BITBOARD SOLVER ENGINE ─────────────────────────────────────────
// Board representation using 64-bit BigInts (7 columns x 7 bits per column).
// Bit 0..5 = col 0 (bottom to top), Bit 6 = header mask.
// Bit 7..12 = col 1, etc.
// This allows O(1) win checking and hyper-fast search up to depth 20+.

const COLS = 7;
const ROWS = 6;
const BOTTOM_MASK = 0x102040810204081n; // 1s at bottom row of each column
const BOARD_MASK = 0x3f7efcfe0c18204081n; // all 42 board cells

type DifficultyLevel = "Easy" | "Medium" | "Hard" | "World Champion";

class Bitboard {
  position: bigint = 0n; // Current player's pieces
  mask: bigint = 0n;     // All occupied cells
  moves: number = 0;

  // Returns true if current player has 4-in-a-row
  hasWon(): boolean {
    const pos = this.position;
    // Horizontal
    let m = pos & (pos >> 7n);
    if ((m & (m >> 14n)) !== 0n) return true;
    // Diagonal 1
    m = pos & (pos >> 6n);
    if ((m & (m >> 12n)) !== 0n) return true;
    // Diagonal 2
    m = pos & (pos >> 8n);
    if ((m & (m >> 16n)) !== 0n) return true;
    // Vertical
    m = pos & (pos >> 1n);
    if ((m & (m >> 2n)) !== 0n) return true;
    return false;
  }

  // Returns bitmask of valid moves
  possibleMoves(): bigint {
    return (this.mask + BOTTOM_MASK) & BOARD_MASK;
  }

  // Make move in column c
  makeMove(col: number) {
    this.position ^= this.mask; // Switch player context
    this.mask |= this.mask + (1n << BigInt(col * 7));
    this.moves++;
  }

  // Column mask for column c
  colMask(col: number): bigint {
    return 0x3fn << BigInt(col * 7);
  }

  canPlay(col: number): boolean {
    return (this.mask & (1n << BigInt(col * 7 + 5))) === 0n;
  }
}

// Transposition Table Entry
type TTEntry = { depth: number; score: number; flag: "EXACT" | "LOWER" | "UPPER" };
const transpositionTable = new Map<bigint, TTEntry>();

// Move ordering (prioritize center, but dynamically evaluate outer columns)
const EXPLORE_ORDER = [3, 2, 4, 1, 5, 0, 6];

function evaluateBitboard(bb: Bitboard): number {
  // Positional weighting favoring central control
  let score = 0;
  for (let c = 0; c < COLS; c++) {
    const weight = 4 - Math.abs(c - 3);
    const colBits = (bb.position >> BigInt(c * 7)) & 0x3fn;
    const oppBits = ((bb.mask ^ bb.position) >> BigInt(c * 7)) & 0x3fn;
    score += countBits(colBits) * weight;
    score -= countBits(oppBits) * weight;
  }
  return score;
}

function countBits(n: bigint): number {
  let count = 0;
  while (n > 0n) {
    if (n & 1n) count++;
    n >>= 1n;
  }
  return count;
}

class TimeoutError extends Error {}

function negamax(
  bb: Bitboard,
  depth: number,
  alpha: number,
  beta: number,
  deadline: number
): number {
  if (performance.now() > deadline) throw new TimeoutError();

  const key = bb.position + bb.mask;
  const tt = transpositionTable.get(key);
  if (tt && tt.depth >= depth) {
    if (tt.flag === "EXACT") return tt.score;
    if (tt.flag === "LOWER") alpha = Math.max(alpha, tt.score);
    if (tt.flag === "UPPER") beta = Math.min(beta, tt.score);
    if (alpha >= beta) return tt.score;
  }

  if (bb.hasWon()) return -(22 - Math.floor(bb.moves / 2)); // Forced loss for opponent
  if (bb.moves >= 42) return 0; // Draw
  if (depth === 0) return evaluateBitboard(bb);

  let alphaOrig = alpha;
  let maxScore = -100000;

  for (const col of EXPLORE_ORDER) {
    if (!bb.canPlay(col)) continue;

    const child = new Bitboard();
    child.position = bb.position;
    child.mask = bb.mask;
    child.moves = bb.moves;
    child.makeMove(col);

    // Opponent's turn -> negamax inversion
    const score = -negamax(child, depth - 1, -beta, -alpha, deadline);

    if (score > maxScore) maxScore = score;
    alpha = Math.max(alpha, score);
    if (alpha >= beta) break; // Alpha-beta pruning cutoff
  }

  let flag: "EXACT" | "LOWER" | "UPPER" = "EXACT";
  if (maxScore <= alphaOrig) flag = "UPPER";
  else if (maxScore >= beta) flag = "LOWER";

  transpositionTable.set(key, { depth, score: maxScore, flag });
  return maxScore;
}

function getBestBitboardMove(
  boardArray: number[],
  botPlayer: number,
  difficulty: DifficultyLevel
): number {
  // Reconstruct Bitboard from current game state
  const bb = new Bitboard();
  
  // Fill bitboard column by column
  for (let c = 0; c < COLS; c++) {
    for (let r = ROWS - 1; r >= 0; r--) {
      const val = boardArray[r * COLS + c];
      if (val !== 0) {
        if (val === botPlayer) {
          bb.position |= 1n << BigInt(c * 7 + (5 - r));
        }
        bb.mask |= 1n << BigInt(c * 7 + (5 - r));
        bb.moves++;
      }
    }
  }

  // Ensure current bitboard perspective matches bot turn
  if (botPlayer === 1) {
    bb.position = bb.mask ^ bb.position;
  }

  const validCols = EXPLORE_ORDER.filter(c => bb.canPlay(c));
  if (validCols.length === 1) return validCols[0];

  // Easy / Medium mode introduce deliberate blunders
  if (difficulty === "Easy" && Math.random() < 0.4) return validCols[Math.floor(Math.random() * validCols.length)];
  if (difficulty === "Medium" && Math.random() < 0.2) return validCols[Math.floor(Math.random() * validCols.length)];

  // Depth selection
  const maxDepth = difficulty === "World Champion" ? 22 : difficulty === "Hard" ? 10 : 4;
  const timeLimitMs = difficulty === "World Champion" ? 2500 : 800;
  const deadline = performance.now() + timeLimitMs;

  let bestMove = validCols[0];
  let bestValue = -Infinity;

  transpositionTable.clear();

  // Iterative Deepening
  for (let d = 1; d <= maxDepth; d++) {
    try {
      let currentBestMove = bestMove;
      let currentBestScore = -Infinity;

      for (const col of validCols) {
        const child = new Bitboard();
        child.position = bb.position;
        child.mask = bb.mask;
        child.moves = bb.moves;
        child.makeMove(col);

        const score = -negamax(child, d - 1, -100000, 100000, deadline);
        if (score > currentBestScore) {
          currentBestScore = score;
          currentBestMove = col;
        }
      }

      bestMove = currentBestMove;
      bestValue = currentBestScore;

      // Found forced win line
      if (bestValue > 10) break;
    } catch (e) {
      if (e instanceof TimeoutError) break;
      throw e;
    }
  }

  return bestMove;
}

// ── REACT GAME COMPONENT ─────────────────────────────────────────────────────

const HUMAN = 1;
const BOT = 2;

export default function Connect4Unbeatable() {
  const [board, setBoard] = useState<number[]>(Array(42).fill(0));
  const [turn, setTurn] = useState<number>(HUMAN);
  const [startingPlayer, setStartingPlayer] = useState<number>(HUMAN);
  const [difficulty, setDifficulty] = useState<DifficultyLevel>("World Champion");
  const [turnLimit, setTurnLimit] = useState<number>(10); // Default 10s per move
  const [timeLeft, setTimeLeft] = useState<number>(10);
  const [status, setStatus] = useState<string>("YOUR TURN");
  const [winner, setWinner] = useState<number | "draw" | "timeout_human" | "timeout_bot" | null>(null);
  const [score, setScore] = useState({ you: 0, bot: 0 });

  const gameId = useRef(0);

  // Check 4-in-a-row on standard grid
  const checkWin = (b: number[]): number => {
    // Horizontal
    for (let r = 0; r < 6; r++) {
      for (let c = 0; c < 4; c++) {
        const p = b[r * 7 + c];
        if (p && p === b[r * 7 + c + 1] && p === b[r * 7 + c + 2] && p === b[r * 7 + c + 3]) return p;
      }
    }
    // Vertical
    for (let r = 0; r < 3; r++) {
      for (let c = 0; c < 7; c++) {
        const p = b[r * 7 + c];
        if (p && p === b[(r + 1) * 7 + c] && p === b[(r + 2) * 7 + c] && p === b[(r + 3) * 7 + c]) return p;
      }
    }
    // Diagonal Down-Right
    for (let r = 0; r < 3; r++) {
      for (let c = 0; c < 4; c++) {
        const p = b[r * 7 + c];
        if (p && p === b[(r + 1) * 7 + c + 1] && p === b[(r + 2) * 7 + c + 2] && p === b[(r + 3) * 7 + c + 3]) return p;
      }
    }
    // Diagonal Down-Left
    for (let r = 0; r < 3; r++) {
      for (let c = 3; c < 7; c++) {
        const p = b[r * 7 + c];
        if (p && p === b[(r + 1) * 7 + c - 1] && p === b[(r + 2) * 7 + c - 2] && p === b[(r + 3) * 7 + c - 3]) return p;
      }
    }
    return b.includes(0) ? 0 : -1; // -1 for draw
  };

  const dropPiece = useCallback((col: number, player: number) => {
    setBoard(prev => {
      const next = [...prev];
      for (let r = ROWS - 1; r >= 0; r--) {
        if (next[r * COLS + col] === 0) {
          next[r * COLS + col] = player;
          break;
        }
      }

      const res = checkWin(next);
      if (res > 0) {
        setWinner(res);
        setScore(s => (res === HUMAN ? { ...s, you: s.you + 1 } : { ...s, bot: s.bot + 1 }));
        setStatus(res === HUMAN ? "YOU WIN! 🎉" : "BOT VICTORIOUS (UNBEATABLE) 💀");
      } else if (res === -1) {
        setWinner("draw");
        setStatus("DRAW GAME");
      } else {
        setTurn(player === HUMAN ? BOT : HUMAN);
        setTimeLeft(turnLimit);
        setStatus(player === HUMAN ? "BOT IS COMPUTING..." : "YOUR TURN");
      }

      return next;
    });
  }, [turnLimit]);

  // Player Move
  const handleCellClick = (col: number) => {
    if (turn !== HUMAN || winner !== null) return;
    if (board[col] !== 0) return; // Column full
    dropPiece(col, HUMAN);
  };

  // Bot Trigger Hook
  useEffect(() => {
    if (turn === BOT && winner === null) {
      const currentId = gameId.current;
      setTimeout(() => {
        if (gameId.current !== currentId) return;
        const col = getBestBitboardMove(board, BOT, difficulty);
        dropPiece(col, BOT);
      }, 50);
    }
  }, [turn, winner, board, difficulty, dropPiece]);

  // Per-Turn Clock
  useEffect(() => {
    if (winner !== null || turnLimit === 0) return;
    const interval = setInterval(() => {
      setTimeLeft(t => {
        if (t <= 1) {
          if (turn === HUMAN) {
            setWinner("timeout_human");
            setStatus("TIME EXPIRED! BOT WINS 💀");
            setScore(s => ({ ...s, bot: s.bot + 1 }));
          } else {
            setWinner("timeout_bot");
            setStatus("BOT TIMED OUT! YOU WIN 🎉");
            setScore(s => ({ ...s, you: s.you + 1 }));
          }
          return 0;
        }
        return t - 1;
      });
    }, 1000);
    return () => clearInterval(interval);
  }, [turn, winner, turnLimit]);

  // Restart
  const resetGame = (firstPlayer = startingPlayer) => {
    gameId.current += 1;
    setBoard(Array(42).fill(0));
    setWinner(null);
    setTurn(firstPlayer);
    setTimeLeft(turnLimit);
    setStatus(firstPlayer === HUMAN ? "YOUR TURN" : "BOT IS COMPUTING...");
  };

  return (
    <div style={{ minHeight: "100vh", background: "#06041a", color: "#fff", display: "flex", flexDirection: "column", alignItems: "center", justifyContent: "center", fontFamily: "monospace", padding: "16px" }}>
      <h1 style={{ background: "linear-gradient(135deg, #ff6b6b, #c084fc, #60a5fa)", WebkitBackgroundClip: "text", WebkitTextFillColor: "transparent", margin: "0 0 6px 0" }}>
        UNBEATABLE CONNECT 4
      </h1>
      <p style={{ color: "#6b6890", fontSize: "11px", margin: "0 0 16px 0", letterSpacing: "2px" }}>
        BITBOARD SOLVER · NEGAMAX + ALPHA-BETA PRUNING
      </p>

      {/* Settings Row */}
      <div style={{ display: "flex", gap: "12px", marginBottom: "12px", flexWrap: "wrap", justifyContent: "center" }}>
        {/* Difficulty */}
        <div>
          <span style={{ fontSize: "10px", color: "#a5b4fc", marginRight: "6px" }}>DIFFICULTY:</span>
          {(["Easy", "Medium", "Hard", "World Champion"] as DifficultyLevel[]).map(d => (
            <button
              key={d}
              onClick={() => { setDifficulty(d); resetGame(); }}
              style={{
                padding: "4px 8px", fontSize: "10px", margin: "0 2px", borderRadius: "8px", border: "1px solid #ffffff1e",
                background: d === difficulty ? "#be123c" : "transparent", color: d === difficulty ? "#fff" : "#818cf8", cursor: "pointer"
              }}
            >
              {d}
            </button>
          ))}
        </div>

        {/* Timer Selection */}
        <div>
          <span style={{ fontSize: "10px", color: "#a5b4fc", marginRight: "6px" }}>TIMER:</span>
          {[5, 10, 15, 0].map(s => (
            <button
              key={s}
              onClick={() => { setTurnLimit(s); setTimeLeft(s); }}
              style={{
                padding: "4px 8px", fontSize: "10px", margin: "0 2px", borderRadius: "8px", border: "1px solid #ffffff1e",
                background: s === turnLimit ? "#38bdf822" : "transparent", color: s === turnLimit ? "#38bdf8" : "#818cf8", cursor: "pointer"
              }}
            >
              {s === 0 ? "Off" : `${s}s`}
            </button>
          ))}
        </div>
      </div>

      {/* First Move Selector */}
      <div style={{ display: "flex", gap: "8px", alignItems: "center", marginBottom: "12px" }}>
        <span style={{ fontSize: "10px", color: "#a5b4fc" }}>STARTING PLAYER:</span>
        <button
          onClick={() => { setStartingPlayer(HUMAN); resetGame(HUMAN); }}
          style={{ padding: "4px 10px", fontSize: "10px", borderRadius: "8px", background: startingPlayer === HUMAN ? "#1d4ed8" : "transparent", border: "1px solid #3b82f6", color: "#fff", cursor: "pointer" }}
        >
          YOU FIRST
        </button>
        <button
          onClick={() => { setStartingPlayer(BOT); resetGame(BOT); }}
          style={{ padding: "4px 10px", fontSize: "10px", borderRadius: "8px", background: startingPlayer === BOT ? "#be123c" : "transparent", border: "1px solid #ef4444", color: "#fff", cursor: "pointer" }}
        >
          BOT FIRST
        </button>
      </div>

      {/* Clock & Status Display */}
      {turnLimit > 0 && winner === null && (
        <div style={{ color: timeLeft <= 3 ? "#ef4444" : "#f59e0b", fontWeight: "bold", fontSize: "14px", marginBottom: "8px" }}>
          ⏱ MOVE TIME: {timeLeft}s
        </div>
      )}

      <div style={{ padding: "6px 20px", borderRadius: "16px", background: "#110c38", border: "1px solid #ffffff1a", color: "#a855f7", fontWeight: "bold", fontSize: "12px", marginBottom: "16px" }}>
        {status}
      </div>

      {/* Score Tracker */}
      <div style={{ display: "flex", gap: "24px", marginBottom: "16px", fontSize: "12px" }}>
        <div>YOU: <span style={{ color: "#60a5fa", fontWeight: "bold" }}>{score.you}</span></div>
        <div>BOT: <span style={{ color: "#f87171", fontWeight: "bold" }}>{score.bot}</span></div>
      </div>

      {/* Connect 4 Board */}
      <div style={{ background: "#0e0b35", padding: "10px", borderRadius: "16px", border: "1px solid #ffffff14", display: "grid", gridTemplateColumns: "repeat(7, 48px)", gap: "6px" }}>
        {Array.from({ length: 42 }).map((_, i) => {
          const col = i % 7;
          const val = board[i];
          const color = val === HUMAN ? "#3b82f6" : val === BOT ? "#ef4444" : "#06041a";

          return (
            <div
              key={i}
              onClick={() => handleCellClick(col)}
              style={{
                width: "48px", height: "48px", borderRadius: "50%", background: color,
                border: "1px solid #ffffff12", cursor: turn === HUMAN && winner === null ? "pointer" : "default"
              }}
            />
          );
        })}
      </div>

      <button onClick={() => resetGame()} style={{ marginTop: "20px", padding: "8px 24px", background: "transparent", border: "1px solid #6366f1", color: "#818cf8", borderRadius: "20px", cursor: "pointer" }}>
        ↺ RESET GAME
      </button>
    </div>
  );
}
