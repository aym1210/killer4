import { useState, useEffect, useCallback, useRef } from "react";

const ROWS = 6;
const COLS = 7;
const EMPTY = 0;
const HUMAN = 1;
const BOT = 2;
const DEPTH = 11;

type Board = number[];
type Result = { winner: number; cells: [number, number][] } | "draw" | null;
type LastMove = { row: number; col: number; player: number } | null;

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
  for (const v of [a,b,c,d]) { if(v===BOT)bot++; else if(v===HUMAN)hum++; }
  if(bot===4)return 500000; if(hum===4)return -500000;
  if(bot===3&&hum===0)return 60; if(bot===2&&hum===0)return 12;
  if(hum===3&&bot===0)return -200; if(hum===2&&bot===0)return -15;
  return 0;
};

const staticScore = (b: Board): number => {
  let s=0;
  for(let i=0;i<ROWS*COLS;i++){if(b[i]===BOT)s+=POS_W[i];else if(b[i]===HUMAN)s-=POS_W[i];}
  for(let r=0;r<ROWS;r++)for(let c=0;c<=COLS-4;c++)s+=scoreWindow4(b[idx(r,c)],b[idx(r,c+1)],b[idx(r,c+2)],b[idx(r,c+3)]);
  for(let c=0;c<COLS;c++)for(let r=0;r<=ROWS-4;r++)s+=scoreWindow4(b[idx(r,c)],b[idx(r+1,c)],b[idx(r+2,c)],b[idx(r+3,c)]);
  for(let r=0;r<=ROWS-4;r++)for(let c=0;c<=COLS-4;c++)s+=scoreWindow4(b[idx(r,c)],b[idx(r+1,c+1)],b[idx(r+2,c+2)],b[idx(r+3,c+3)]);
  for(let r=0;r<=ROWS-4;r++)for(let c=3;c<COLS;c++)s+=scoreWindow4(b[idx(r,c)],b[idx(r+1,c-1)],b[idx(r+2,c-2)],b[idx(r+3,c-3)]);
  return s;
};

const COL_ORDER = [3,2,4,1,5,0,6];

const minimax = (b: Board, depth: number, alpha: number, beta: number, maximizing: boolean): { score: number; col?: number } => {
  const valid = COL_ORDER.filter(c => b[idx(0,c)] === EMPTY);
  if (!valid.length) return { score: 0 };
  if (depth === 0) return { score: staticScore(b) };
  const player = maximizing ? BOT : HUMAN;
  const opp = maximizing ? HUMAN : BOT;
  const wins: number[] = [], blocks: number[] = [], rest: number[] = [];
  for (const c of valid) {
    const r = getRow(b, c);
    b[idx(r,c)] = player; const iw = !!checkWinAt(b,r,c,player); b[idx(r,c)] = EMPTY;
    if (iw) { wins.push(c); continue; }
    b[idx(r,c)] = opp; const ib = !!checkWinAt(b,r,c,opp); b[idx(r,c)] = EMPTY;
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
      else score = minimax(b, depth-1, alpha, beta, false).score;
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
      else score = minimax(b, depth-1, alpha, beta, true).score;
      undrop(b, col, r);
      if (score < best.score) best = { score, col };
      beta = Math.min(beta, score);
      if (alpha >= beta) break;
    }
    return best;
  }
};

const getBotMove = (board: Board): number => {
  const b = cloneBoard(board);
  for (const c of getValidCols(b)) { const r=dropMut(b,c,BOT); const w=checkWinAt(b,r,c,BOT); undrop(b,c,r); if(w) return c; }
  for (const c of getValidCols(b)) { const r=dropMut(b,c,HUMAN); const w=checkWinAt(b,r,c,HUMAN); undrop(b,c,r); if(w) return c; }
  const res = minimax(b, DEPTH, -Infinity, Infinity, true);
  return res.col ?? getValidCols(board)[0];
};

const NUM_PARTICLES = 18;
const PARTICLES = Array.from({length: NUM_PARTICLES}, (_, i) => ({
  id: i, x: Math.random()*100, y: Math.random()*100,
  size: 1.5+Math.random()*3, dur: 6+Math.random()*10,
  delay: Math.random()*8, opacity: 0.15+Math.random()*0.3,
}));

export default function Connect4() {
  const [board, setBoard] = useState<Board>(() => createBoard());
  const [turn, setTurn] = useState<number>(HUMAN);
  const [result, setResult] = useState<Result>(null);
  const [hoverCol, setHoverCol] = useState<number | null>(null);
  const [thinking, setThinking] = useState(false);
  const [lastMove, setLastMove] = useState<LastMove>(null);
  const [score, setScore] = useState({ you: 0, bot: 0 });
  const [moveCount, setMoveCount] = useState(0);
  const pendingBot = useRef(false);

  const tryFinalize = (b: Board, row: number, col: number, player: number): boolean => {
    const winCells = checkWinAt(b, row, col, player);
    if (winCells) {
      setResult({ winner: player, cells: winCells });
      setScore(s => player === HUMAN ? {...s, you: s.you+1} : {...s, bot: s.bot+1});
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
    setBoard(b); setLastMove({row,col,player:HUMAN}); setMoveCount(n=>n+1);
    if (!tryFinalize(b, row, col, HUMAN)) setTurn(BOT);
  }, [board, turn, result, thinking]);

  useEffect(() => {
    if (turn !== BOT || result || pendingBot.current) return;
    pendingBot.current = true;
    setThinking(true);
    setTimeout(() => {
      const snap = cloneBoard(board);
      const col = getBotMove(snap);
      const b = cloneBoard(snap);
      const row = dropMut(b, col, BOT);
      setBoard(b); setLastMove({row,col,player:BOT}); setMoveCount(n=>n+1);
      setThinking(false); pendingBot.current = false;
      if (!tryFinalize(b, row, col, BOT)) setTurn(HUMAN);
    }, 60);
  }, [turn, result]);

  const reset = () => {
    pendingBot.current = false;
    setBoard(createBoard()); setTurn(HUMAN); setResult(null);
    setHoverCol(null); setThinking(false); setLastMove(null); setMoveCount(0);
  };

  const winSet = new Set(
    result && result !== "draw" ? result.cells.map(([r,c]) => `${r},${c}`) : []
  );

  const accentColor = result && result !== "draw" && result.winner === HUMAN ? "#22c55e"
    : result && result !== "draw" && result.winner === BOT ? "#ef4444"
    : result === "draw" ? "#f59e0b"
    : thinking ? "#a855f7" : "#3b82f6";

  const statusMsg = () => {
    if (result === "draw") return "DRAW";
    if (result && result !== "draw" && result.winner === HUMAN) return "YOU WIN! 🎉";
    if (result && result !== "draw" && result.winner === BOT) return "ANNIHILATED 💀";
    if (thinking) return "THINKING...";
    return "YOUR MOVE";
  };

  const cellSize = typeof window !== "undefined" && window.innerWidth < 480 ? 42 : 52;
  const gap = 5;
  const boardPad = 10;

  return (
    <div style={{
      minHeight:"100vh", width:"100%",
      background:"linear-gradient(135deg,#0a0015 0%,#06001a 40%,#100010 70%,#1a0005 100%)",
      display:"flex", flexDirection:"column", alignItems:"center", justifyContent:"center",
      fontFamily:"'Courier New',monospace", padding:"12px 8px",
      userSelect:"none", position:"relative", overflow:"hidden", boxSizing:"border-box",
    }}>
      <div style={{position:"absolute",inset:0,pointerEvents:"none",zIndex:0}}>
        <div style={{position:"absolute",inset:0,background:"radial-gradient(ellipse 80% 60% at 15% 20%,#1a003388 0%,transparent 60%),radial-gradient(ellipse 60% 50% at 85% 75%,#00001a99 0%,transparent 55%),radial-gradient(ellipse 50% 40% at 50% 50%,#0d001a44 0%,transparent 70%)"}}/>
        <div style={{position:"absolute",top:"-10%",right:"-5%",width:"55%",height:"55%",background:"radial-gradient(ellipse,#8b000055 0%,#4a000033 40%,transparent 70%)",filter:"blur(40px)",animation:"nebulaDrift1 18s ease-in-out infinite alternate"}}/>
        <div style={{position:"absolute",bottom:"-15%",left:"-10%",width:"65%",height:"60%",background:"radial-gradient(ellipse,#00008b44 0%,#00004422 50%,transparent 75%)",filter:"blur(50px)",animation:"nebulaDrift2 22s ease-in-out infinite alternate"}}/>
        <div style={{position:"absolute",top:"40%",left:"30%",width:"45%",height:"40%",background:"radial-gradient(ellipse,#33003322 0%,transparent 65%)",filter:"blur(35px)",animation:"nebulaDrift3 15s ease-in-out infinite alternate"}}/>
        <div style={{position:"absolute",top:"20%",left:"50%",transform:"translateX(-50%)",width:"60%",height:"30%",background:`radial-gradient(ellipse,${accentColor}18 0%,transparent 70%)`,filter:"blur(30px)",transition:"background 1s ease"}}/>
        <div style={{position:"absolute",inset:0,backgroundImage:"linear-gradient(rgba(99,102,241,0.025) 1px,transparent 1px),linear-gradient(90deg,rgba(99,102,241,0.025) 1px,transparent 1px)",backgroundSize:"48px 48px"}}/>
        <div style={{position:"absolute",inset:0,backgroundImage:"repeating-linear-gradient(0deg,transparent,transparent 2px,rgba(0,0,0,0.06) 2px,rgba(0,0,0,0.06) 4px)"}}/>
        {PARTICLES.map(p=>(
          <div key={p.id} style={{position:"absolute",left:`${p.x}%`,top:`${p.y}%`,width:`${p.size}px`,height:`${p.size}px`,borderRadius:"50%",background:p.id%3===0?"#ff4444":p.id%3===1?"#4488ff":"#ffffff",opacity:p.opacity,animation:`starFloat ${p.dur}s ${p.delay}s ease-in-out infinite alternate`}}/>
        ))}
      </div>

      <div style={{textAlign:"center",marginBottom:"14px",position:"relative",zIndex:1}}>
        <div style={{fontSize:"clamp(20px,6vw,46px)",fontWeight:900,letterSpacing:"0.2em",lineHeight:1,background:"linear-gradient(135deg,#ff6b6b 0%,#c084fc 45%,#60a5fa 100%)",WebkitBackgroundClip:"text",WebkitTextFillColor:"transparent",textTransform:"uppercase",filter:"drop-shadow(0 0 20px #c084fc44)"}}>CONNECT FOUR</div>
        <div style={{color:"#4a3060",fontSize:"9px",letterSpacing:"0.35em",marginTop:"3px"}}>DEPTH {DEPTH} · ALPHA-BETA · KILLER ORDERING</div>
      </div>

      <div style={{display:"flex",gap:"0",marginBottom:"10px",position:"relative",zIndex:1,border:"1px solid #ffffff0f",borderRadius:"6px",overflow:"hidden",background:"rgba(0,0,0,0.35)",backdropFilter:"blur(8px)"}}>
        {([["YOU",score.you,"#60a5fa","#1e3a5f22"],["MOVES",moveCount,"#a78bfa","#2d1b6922"],["BOT",score.bot,"#f87171","#5f1e1e22"]] as [string,number,string,string][]).map(([label,val,color,bg],i)=>(
          <div key={label} style={{padding:"7px 18px",textAlign:"center",background:bg,borderRight:i<2?"1px solid #ffffff0a":"none"}}>
            <div style={{color:"#ffffff33",fontSize:"8px",letterSpacing:"0.3em"}}>{label}</div>
            <div style={{color,fontSize:"16px",fontWeight:900,lineHeight:1.2}}>{val}</div>
          </div>
        ))}
      </div>

      <div style={{marginBottom:"10px",padding:"7px 20px",border:`1px solid ${accentColor}44`,background:`${accentColor}12`,backdropFilter:"blur(6px)",color:accentColor,fontSize:"11px",letterSpacing:"0.15em",fontWeight:700,borderRadius:"20px",transition:"all 0.4s",display:"flex",alignItems:"center",gap:"8px",position:"relative",zIndex:1}}>
        {thinking&&[0,1,2].map(i=>(
          <span key={i} style={{display:"inline-block",width:"4px",height:"4px",borderRadius:"50%",background:"#a855f7",animation:`blink 0.8s ${i*0.22}s infinite`}}/>
        ))}
        {statusMsg()}
      </div>

      <div style={{position:"relative",zIndex:1}}>
        <div style={{display:"flex",gap:`${gap}px`,marginBottom:"4px",paddingLeft:`${boardPad}px`,paddingRight:`${boardPad}px`}}>
          {Array.from({length:COLS},(_,c)=>{
            const active=hoverCol===c&&turn===HUMAN&&!result&&!thinking;
            const full=board[idx(0,c)]!==EMPTY;
            return (
              <div key={c} style={{width:`${cellSize}px`,height:"14px",display:"flex",alignItems:"center",justifyContent:"center"}}>
                {active&&!full&&<div style={{width:0,height:0,borderLeft:"6px solid transparent",borderRight:"6px solid transparent",borderTop:`9px solid ${accentColor}`,filter:`drop-shadow(0 0 4px ${accentColor})`,animation:"arrowDrop 0.4s ease-in-out infinite alternate"}}/>}
                {active&&full&&<span style={{color:"#ef4444",fontSize:"11px"}}>✕</span>}
              </div>
            );
          })}
        </div>

        <div style={{background:"linear-gradient(160deg,#0e0b35ee,#08062aee)",borderRadius:"16px",padding:`${boardPad}px`,border:"1px solid #ffffff0d",boxShadow:`0 0 0 1px #3730a322,0 0 60px #1a0d4422,0 24px 60px rgba(0,0,0,0.7),inset 0 1px 0 #ffffff08,0 0 30px ${accentColor}22`,backdropFilter:"blur(4px)",transition:"box-shadow 0.5s"}}>
          {Array.from({length:ROWS},(_,r)=>(
            <div key={r} style={{display:"flex",gap:`${gap}px`,marginBottom:r<ROWS-1?`${gap}px`:0}}>
              {Array.from({length:COLS},(_,c)=>{
                const cell=board[idx(r,c)];
                const isWin=winSet.has(`${r},${c}`);
                const isLast=lastMove?.row===r&&lastMove?.col===c;
                const hovering=hoverCol===c&&!result&&!thinking&&turn===HUMAN&&cell===EMPTY;
                const colFull=board[idx(0,c)]!==EMPTY;
                let fill="transparent",glow="transparent";
                if(cell===HUMAN){fill=isWin?"linear-gradient(145deg,#86efac,#16a34a)":"linear-gradient(145deg,#93c5fd,#1d4ed8)";glow=isWin?"#16a34a":"#1d4ed8";}
                else if(cell===BOT){fill=isWin?"linear-gradient(145deg,#fca5a5,#b91c1c)":"linear-gradient(145deg,#fda4af,#be123c)";glow=isWin?"#b91c1c":"#be123c";}
                return (
                  <div key={c} onClick={()=>handleDrop(c)} onMouseEnter={()=>setHoverCol(c)} onMouseLeave={()=>setHoverCol(null)}
                    style={{width:`${cellSize}px`,height:`${cellSize}px`,borderRadius:"50%",background:hovering?"#1c1950":"#06041a",border:isLast&&cell!==EMPTY?`2px solid ${glow}bb`:hovering?`2px solid ${accentColor}44`:"2px solid #ffffff07",cursor:turn===HUMAN&&!result&&!thinking&&!colFull?"pointer":"default",display:"flex",alignItems:"center",justifyContent:"center",transition:"background 0.1s,border-color 0.1s",boxShadow:"inset 0 3px 12px rgba(0,0,0,0.8)",flexShrink:0}}>
                    {cell!==EMPTY&&(
                      <div style={{width:`${cellSize-10}px`,height:`${cellSize-10}px`,borderRadius:"50%",background:fill,boxShadow:isWin?`0 0 20px ${glow},0 0 40px ${glow}66,inset 0 -2px 5px rgba(0,0,0,0.4),inset 0 2px 5px rgba(255,255,255,0.2)`:`0 0 ${isLast?12:4}px ${glow}${isLast?"cc":"44"},inset 0 -2px 5px rgba(0,0,0,0.35),inset 0 2px 5px rgba(255,255,255,0.18)`,animation:isWin?"winPulse 0.7s ease-in-out infinite alternate":isLast?"dropIn 0.25s cubic-bezier(0.34,1.56,0.64,1) both":"none"}}/>
                    )}
                  </div>
                );
              })}
            </div>
          ))}
        </div>
      </div>

      <div style={{display:"flex",alignItems:"center",gap:"20px",marginTop:"14px",position:"relative",zIndex:1,flexWrap:"wrap",justifyContent:"center"}}>
        {(([["YOU","#1d4ed8","#60a5fa"],["BOT","#be123c","#f87171"]] as [string,string,string][]).map(([label,bg,text])=>(
          <div key={label} style={{display:"flex",alignItems:"center",gap:"6px",fontSize:"11px",letterSpacing:"0.12em"}}>
            <div style={{width:"12px",height:"12px",borderRadius:"50%",background:bg,boxShadow:`0 0 8px ${bg}`}}/>
            <span style={{color:text}}>{label}</span>
          </div>
        )))}
        <button onClick={reset}
          onMouseEnter={e=>{(e.currentTarget as HTMLButtonElement).style.background="#c084fc22";(e.currentTarget as HTMLButtonElement).style.borderColor="#c084fc";(e.currentTarget as HTMLButtonElement).style.color="#e0aaff";}}
          onMouseLeave={e=>{(e.currentTarget as HTMLButtonElement).style.background="transparent";(e.currentTarget as HTMLButtonElement).style.borderColor="#6366f166";(e.currentTarget as HTMLButtonElement).style.color="#818cf8";}}
          style={{padding:"7px 22px",background:"transparent",border:"1px solid #6366f166",color:"#818cf8",borderRadius:"20px",cursor:"pointer",fontSize:"11px",letterSpacing:"0.18em",textTransform:"uppercase",fontFamily:"'Courier New',monospace",transition:"all 0.2s"}}>
          ↺ NEW GAME
        </button>
      </div>

      {result&&(
        <div onClick={reset} style={{position:"fixed",inset:0,zIndex:50,background:"rgba(0,0,0,0.72)",backdropFilter:"blur(6px)",display:"flex",flexDirection:"column",alignItems:"center",justifyContent:"center",cursor:"pointer"}}>
          <div style={{position:"absolute",width:"300px",height:"300px",borderRadius:"50%",background:`radial-gradient(circle,${result==="draw"?"#f59e0b":result!=="draw"&&result.winner===HUMAN?"#22c55e":"#ef4444"}33 0%,transparent 70%)`,filter:"blur(30px)"}}/>
          <div style={{fontSize:"clamp(56px,12vw,110px)",fontWeight:900,letterSpacing:"0.08em",textTransform:"uppercase",color:result==="draw"?"#fbbf24":result!=="draw"&&result.winner===HUMAN?"#4ade80":"#f87171",textShadow:"0 0 60px currentColor,0 0 120px currentColor",animation:"popIn 0.45s cubic-bezier(0.34,1.56,0.64,1) both",position:"relative"}}>
            {result==="draw"?"DRAW":result!=="draw"&&result.winner===HUMAN?"WIN!":"LOSE"}
          </div>
          <div style={{color:"#ffffff33",fontSize:"11px",marginTop:"16px",letterSpacing:"0.3em",position:"relative"}}>TAP TO PLAY AGAIN</div>
        </div>
      )}

      <style>{`
        @keyframes dropIn { from{transform:scale(0.3) translateY(-12px);opacity:0} to{transform:scale(1) translateY(0);opacity:1} }
        @keyframes winPulse { from{transform:scale(0.88);filter:brightness(0.9)} to{transform:scale(1.12);filter:brightness(1.4)} }
        @keyframes blink { 0%,100%{opacity:0.15;transform:scale(0.6)} 50%{opacity:1;transform:scale(1.3)} }
        @keyframes arrowDrop { from{transform:translateY(0);opacity:0.7} to{transform:translateY(5px);opacity:1} }
        @keyframes popIn { from{opacity:0;transform:scale(0.35)} to{opacity:1;transform:scale(1)} }
        @keyframes nebulaDrift1 { from{transform:translate(0,0) scale(1);opacity:0.7} to{transform:translate(-4%,3%) scale(1.08);opacity:1} }
        @keyframes nebulaDrift2 { from{transform:translate(0,0) scale(1);opacity:0.6} to{transform:translate(3%,-4%) scale(1.1);opacity:0.9} }
        @keyframes nebulaDrift3 { from{transform:translate(0,0);opacity:0.5} to{transform:translate(-2%,2%);opacity:0.8} }
        @keyframes starFloat { from{transform:translate(0,0) scale(1)} to{transform:translate(6px,-8px) scale(1.3)} }
        *{box-sizing:border-box}
      `}</style>
    </div>
  );
}