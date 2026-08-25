
(function(){
  "use strict";

  // ---------- audio engine ----------
  var audioCtx = null;
  var humOsc = null, humGain = null;

  function getAudioCtx(){
    if (!audioCtx) {
      var AudioContextClass = window.AudioContext || window.webkitAudioContext;
      if (AudioContextClass) audioCtx = new AudioContextClass();
    }
    if (audioCtx && audioCtx.state === 'suspended') {
      audioCtx.resume();
    }
    return audioCtx;
  }

  function startHum(){
    var ctx = getAudioCtx();
    if (!ctx || humOsc) return;
    try {
      humOsc = ctx.createOscillator();
      humGain = ctx.createGain();
      humOsc.type = 'sine';
      humOsc.frequency.setValueAtTime(55, ctx.currentTime);
      var filter = ctx.createBiquadFilter();
      filter.type = 'lowpass';
      filter.frequency.setValueAtTime(120, ctx.currentTime);

      humGain.gain.setValueAtTime(0.02, ctx.currentTime);

      humOsc.connect(filter);
      filter.connect(humGain);
      humGain.connect(ctx.destination);
      humOsc.start();
    } catch(e){}
  }

  function stopHum(){
    if (humOsc) {
      try { humOsc.stop(); } catch(e){}
      humOsc = null;
    }
  }

  function playSelectSound(pitchIdx){
    var ctx = getAudioCtx();
    if (!ctx) return;
    try {
      var osc = ctx.createOscillator();
      var gain = ctx.createGain();
      osc.type = 'sine';
      var freq = 340 + (pitchIdx || 0) * 45;
      osc.frequency.setValueAtTime(freq, ctx.currentTime);
      osc.frequency.exponentialRampToValueAtTime(freq * 1.3, ctx.currentTime + 0.04);
      gain.gain.setValueAtTime(0.08, ctx.currentTime);
      gain.gain.exponentialRampToValueAtTime(0.001, ctx.currentTime + 0.05);
      osc.connect(gain);
      gain.connect(ctx.destination);
      osc.start();
      osc.stop(ctx.currentTime + 0.05);
    } catch(e){}
  }

  function playDeselectSound(){
    var ctx = getAudioCtx();
    if (!ctx) return;
    try {
      var osc = ctx.createOscillator();
      var gain = ctx.createGain();
      osc.type = 'triangle';
      osc.frequency.setValueAtTime(300, ctx.currentTime);
      osc.frequency.exponentialRampToValueAtTime(150, ctx.currentTime + 0.04);
      gain.gain.setValueAtTime(0.06, ctx.currentTime);
      gain.gain.exponentialRampToValueAtTime(0.001, ctx.currentTime + 0.04);
      osc.connect(gain);
      gain.connect(ctx.destination);
      osc.start();
      osc.stop(ctx.currentTime + 0.04);
    } catch(e){}
  }

  function playEnterSound(){
    var ctx = getAudioCtx();
    if (!ctx) return;
    try {
      var osc = ctx.createOscillator();
      var gain = ctx.createGain();
      osc.type = 'square';
      osc.frequency.setValueAtTime(440, ctx.currentTime);
      osc.frequency.setValueAtTime(880, ctx.currentTime + 0.05);
      gain.gain.setValueAtTime(0.04, ctx.currentTime);
      gain.gain.exponentialRampToValueAtTime(0.001, ctx.currentTime + 0.12);
      osc.connect(gain);
      gain.connect(ctx.destination);
      osc.start();
      osc.stop(ctx.currentTime + 0.12);
    } catch(e){}
  }

  // ---------- config ----------
  var COLS = 6, ROWS = 7;
  var RUN_SECONDS = 75;
  var TARGET_GB = 500;
  var COMBO_WINDOW_MS = 2600;
  var MIN_CHAIN = 3;
  var BUS_CHAIN_THRESHOLD = 10;
  var TRACE_JACKOUT_REDUCTION = 55;
  var BREACH_SEQUENCE_LEN = 3;
  var BREACH_REVEAL_MS = 550;
  var BREACH_TIME_LIMIT_MS = 6000;
  var BREACH_SUCCESS_GB = 40;
  var BREACH_SUCCESS_SCORE = 150;
  var BREACH_FAIL_TRACE = 8;
  var HOP_MS = 90;

  var TYPES = ["security","encrypted","system","power","crypto","schematic"];
  var META = {
    security:  { glyph:"▲", value:5,  gb:2.0, weight:20 },
    encrypted: { glyph:"◈", value:8,  gb:2.6, weight:16 },
    system:    { glyph:"▣", value:4,  gb:1.6, weight:22 },
    power:     { glyph:"⚡", value:6,  gb:2.2, weight:18 },
    crypto:    { glyph:"◎", value:10, gb:3.4, weight:14 },
    schematic: { glyph:"⬡", value:13, gb:4.2, weight:10 },
    bus:       { glyph:"◇", value:15, gb:5.0 }
  };
  var START_ROW = ROWS - 1, START_COL = Math.floor(COLS / 2);

  function weightedType(){
    var securityBoost = trace >= 90 ? 2.6 : (trace >= 75 ? 1.6 : 1);
    var total = 0, k;
    for (k in META){
      if (k === "bus") continue;
      total += META[k].weight * (k === "security" ? securityBoost : 1);
    }
    var r = Math.random() * total;
    for (k in META){
      if (k === "bus") continue;
      var w = META[k].weight * (k === "security" ? securityBoost : 1);
      r -= w;
      if (r <= 0) return k;
    }
    return "system";
  }

  // ---------- state ----------
  var grid = [];              // grid[row][col] = type string ('security'...'bus')
  var score = 0;
  var bankedGB = 0;
  var unbankedGB = 0;
  var trace = 0;
  var maxTrace = 0;
  var objectiveComplete = false;
  var objectiveCompletedAtElapsed = null;
  var extractionCount = 0;
  var dataLostToTrace = 0;
  var busOverridesUsedTotal = 0;

  var combo = 0;
  var maxCombo = 0;
  var lastClearTime = 0;
  var timeLeft = RUN_SECONDS;
  var timerHandle = null;
  var running = false;

  var chain = [];             // array of {row,col,type}
  var dragging = false;
  var busArmedFlashed = false;

  var typeClearCounts = {};
  var chainLengths = [];

  var playerPosition = { row: START_ROW, col: START_COL };

  // ---------- dom refs ----------
  var boardEl = document.getElementById("board");
  var pathwaysLayer = document.getElementById("pathwaysLayer");
  var nodesLayer = document.getElementById("nodesLayer");
  var lineLayer = document.getElementById("linelayer");
  var avatarLayer = document.getElementById("avatarLayer");
  var avatarAnchor = document.getElementById("avatarAnchor");
  var avatarFacing = document.getElementById("avatarFacing");
  var avatarFigure = document.getElementById("avatarFigure");
  var feedbackEl = document.getElementById("feedback");
  var scoreVal = document.getElementById("scoreVal");
  var traceVal = document.getElementById("traceVal");
  var timerVal = document.getElementById("timerVal");
  var dataVal = document.getElementById("dataVal");
  var objLabel = document.getElementById("objLabel");
  var objBar = document.getElementById("objBar");
  var bankedVal = document.getElementById("bankedVal");
  var onboardVal = document.getElementById("onboardVal");
  var jackOutBtn = document.getElementById("jackOutBtn");
  var abandonBtn = document.getElementById("abandonBtn");
  var abandonArmed = false;
  var abandonArmTimeout = null;
  var titleScreen = document.getElementById("title-screen");
  var startBtn = document.getElementById("startBtn");
  var profileBtn = document.getElementById("profileBtn");
  var profileOverlay = document.getElementById("profile-overlay");
  var saveProfileBtn = document.getElementById("saveProfileBtn");
  var summaryOverlay = document.getElementById("summary-overlay");
  var reconnectBtn = document.getElementById("reconnectBtn");
  var breachOverlay = document.getElementById("breach-overlay");
  var breachSlotsEl = document.getElementById("breachSlots");
  var breachKeysEl = document.getElementById("breachKeys");
  var breachResultEl = document.getElementById("breachResult");
  var breachTimerFill = document.getElementById("breachTimerFill");
  var breachActive = false;

  nodesLayer.style.gridTemplateColumns = "repeat(" + COLS + ", 1fr)";
  nodesLayer.style.gridTemplateRows = "repeat(" + ROWS + ", 1fr)";

  // ---------- init ----------
  function newGrid(){
    grid = [];
    for (var r = 0; r < ROWS; r++){
      var row = [];
      for (var c = 0; c < COLS; c++) row.push(weightedType());
      grid.push(row);
    }
  }

  function resetTypeCounts(){
    typeClearCounts = { security:0, encrypted:0, system:0, power:0, crypto:0, schematic:0, bus:0 };
  }

  function resetRun(){
    trace = 0; // must be reset before newGrid() since weightedType() reads trace
    newGrid();
    score = 0; bankedGB = 0; unbankedGB = 0;
    maxTrace = 0; objectiveComplete = false; objectiveCompletedAtElapsed = null;
    extractionCount = 0; dataLostToTrace = 0; busOverridesUsedTotal = 0;
    combo = 0; maxCombo = 0; lastClearTime = 0;
    timeLeft = RUN_SECONDS; running = true;
    resetTypeCounts();
    chainLengths = [];
    chain = []; dragging = false; busArmedFlashed = false;
    summaryOverlay.classList.add("hidden");
    render();
    renderPathways();
    clearTrails();
    placeAvatarInstant(START_ROW, START_COL);
    updateHud();
    clearInterval(timerHandle);
    timerHandle = setInterval(tick, 1000);
    startHum();
  }

  // ---------- rendering ----------
  function render(){
    var html = "";
    for (var r = 0; r < ROWS; r++){
      for (var c = 0; c < COLS; c++){
        var t = grid[r][c];
        var delay = (r * 28) + "ms";
        var hostile = (t === "security" && trace >= 75) ? " hostile" : "";
        html += '<div class="node' + hostile + '" data-type="' + t + '" data-row="' + r + '" data-col="' + c +
                '" style="animation-delay:' + delay + '"><span class="glyph">' + META[t].glyph + '</span></div>';
      }
    }
    nodesLayer.innerHTML = html;
  }

  function cellEl(row, col){
    return nodesLayer.querySelector('[data-row="' + row + '"][data-col="' + col + '"]');
  }

  function cellCenter(row, col){
    var el = cellEl(row, col);
    if (!el) return { x: 0, y: 0 };
    return {
      x: el.offsetLeft + el.offsetWidth / 2,
      y: el.offsetTop + el.offsetHeight / 2
    };
  }

  function renderPathways(){
    var w = boardEl.offsetWidth, h = boardEl.offsetHeight;
    if (!w || !h) return;
    pathwaysLayer.setAttribute("viewBox", "0 0 " + w + " " + h);
    pathwaysLayer.setAttribute("width", w);
    pathwaysLayer.setAttribute("height", h);
    var parts = [];
    for (var r = 0; r < ROWS; r++){
      for (var c = 0; c < COLS; c++){
        var p1 = cellCenter(r, c);
        if (c + 1 < COLS){
          var p2 = cellCenter(r, c + 1);
          parts.push('<line x1="' + p1.x + '" y1="' + p1.y + '" x2="' + p2.x + '" y2="' + p2.y +
            '" stroke="rgba(43,233,255,0.16)" stroke-width="1.5" stroke-linecap="round"/>');
        }
        if (r + 1 < ROWS){
          var p3 = cellCenter(r + 1, c);
          parts.push('<line x1="' + p1.x + '" y1="' + p1.y + '" x2="' + p3.x + '" y2="' + p3.y +
            '" stroke="rgba(43,233,255,0.16)" stroke-width="1.5" stroke-linecap="round"/>');
        }
        parts.push('<circle cx="' + p1.x + '" cy="' + p1.y + '" r="1.6" fill="rgba(43,233,255,0.28)"/>');
      }
    }
    pathwaysLayer.innerHTML = parts.join("");
  }

  function setSelected(){
    var all = nodesLayer.querySelectorAll(".node");
    all.forEach(function(el){ el.classList.remove("selected"); });
    chain.forEach(function(n){
      var el = cellEl(n.row, n.col);
      if (el) el.classList.add("selected");
    });
    drawLine();
  }

  function drawLine(){
    if (chain.length < 2){
      lineLayer.innerHTML = "";
      return;
    }
    var w = boardEl.offsetWidth, h = boardEl.offsetHeight;
    lineLayer.setAttribute("viewBox", "0 0 " + w + " " + h);
    lineLayer.setAttribute("width", w);
    lineLayer.setAttribute("height", h);
    var strokeColor = getComputedStyle(document.documentElement).getPropertyValue("--cyan").trim();
    var pts = chain.map(function(n){
      var p = cellCenter(n.row, n.col);
      return p.x + "," + p.y;
    }).join(" ");
    lineLayer.innerHTML =
      '<polyline points="' + pts + '" fill="none" stroke="' + strokeColor + '" ' +
      'stroke-width="3" stroke-linecap="round" stroke-linejoin="round" stroke-dasharray="1 7" opacity="0.9" ' +
      'style="filter:drop-shadow(0 0 5px ' + strokeColor + ')"></polyline>';
  }

  // ---------- avatar ----------
  function clearTrails(){
    avatarLayer.querySelectorAll(".trail-dot").forEach(function(d){ d.remove(); });
  }

  function placeAvatarInstant(row, col){
    playerPosition = { row: row, col: col };
    var p = cellCenter(row, col);
    avatarAnchor.style.transition = "none";
    avatarAnchor.style.transform = "translate(" + p.x + "px," + p.y + "px)";
    void avatarAnchor.offsetWidth; // force reflow so transition removal takes effect next frame
    avatarAnchor.style.transition = "";
  }

  function moveAvatarTo(row, col){
    var p = cellCenter(row, col);
    avatarAnchor.style.transform = "translate(" + p.x + "px," + p.y + "px)";
  }

  function pulseNode(row, col){
    var el = cellEl(row, col);
    if (!el) return;
    el.classList.add("avatar-pulse");
    setTimeout(function(){ el.classList.remove("avatar-pulse"); }, 320);
  }

  function spawnTrail(row, col){
    var p = cellCenter(row, col);
    var dot = document.createElement("div");
    dot.className = "trail-dot";
    dot.style.left = p.x + "px";
    dot.style.top = p.y + "px";
    avatarLayer.appendChild(dot);
    setTimeout(function(){ if (dot.parentNode) dot.parentNode.removeChild(dot); }, 520);
  }

  function updateFacing(fromPos, toPos){
    var dx = toPos.col - fromPos.col;
    if (dx !== 0) avatarFacing.classList.toggle("flip", dx < 0);
  }

  function animateAvatarPath(path){
    var startPos = { row: playerPosition.row, col: playerPosition.col };
    var i = 0;
    if (path.length > 0) avatarFigure.classList.add("walking");
    function step(){
      if (i >= path.length){
        avatarFigure.classList.remove("walking");
        avatarFigure.classList.add("arrive");
        setTimeout(function(){ avatarFigure.classList.remove("arrive"); }, 320);
        return;
      }
      var n = path[i];
      var prev = i > 0 ? path[i - 1] : startPos;
      updateFacing(prev, n);
      if (i > 0) spawnTrail(path[i - 1].row, path[i - 1].col);
      moveAvatarTo(n.row, n.col);
      pulseNode(n.row, n.col);
      playerPosition = { row: n.row, col: n.col };
      i++;
      setTimeout(step, HOP_MS);
    }
    step();
  }

  // ---------- HUD ----------
  function updateHud(){
    scoreVal.textContent = score;

    var mm = Math.floor(timeLeft / 60), ss = timeLeft % 60;
    timerVal.textContent = (mm < 10 ? "0" : "") + mm + ":" + (ss < 10 ? "0" : "") + ss;
    timerVal.classList.toggle("warn", timeLeft <= 10);

    traceVal.textContent = Math.round(trace) + "%";
    traceVal.classList.remove("trace-elevated","trace-warning","trace-critical");
    if (trace >= 90) traceVal.classList.add("trace-critical");
    else if (trace >= 75) traceVal.classList.add("trace-warning");
    else if (trace >= 50) traceVal.classList.add("trace-elevated");

    var totalSecured = bankedGB + unbankedGB;
    dataVal.textContent = Math.floor(totalSecured) + " / " + TARGET_GB + " GB";
    var pct = Math.min(100, (totalSecured / TARGET_GB) * 100);
    objBar.style.width = pct + "%";
    objBar.classList.toggle("complete", objectiveComplete);
    objLabel.textContent = objectiveComplete ? "OBJECTIVE COMPLETE // EXTRACTION AVAILABLE" : "OBJECTIVE — EXFILTRATE DATA";

    bankedVal.textContent = Math.floor(bankedGB) + " GB";
    onboardVal.textContent = Math.floor(unbankedGB) + " GB";

    if (objectiveComplete){
      jackOutBtn.textContent = "JACK OUT // BANK LOOT";
      jackOutBtn.disabled = false;
      jackOutBtn.classList.add("primary");
      jackOutBtn.classList.toggle("urgent", trace >= 75);
    } else {
      jackOutBtn.textContent = "OBJECTIVE INCOMPLETE";
      jackOutBtn.disabled = true;
      jackOutBtn.classList.remove("primary","urgent");
    }
  }

  function floatText(text, cls){
    var el = document.createElement("div");
    el.className = "floater " + cls;
    el.textContent = text;
    feedbackEl.innerHTML = "";
    feedbackEl.appendChild(el);
    setTimeout(function(){ if (el.parentNode) el.parentNode.removeChild(el); }, 900);
  }

  function toast(text){
    var el = document.createElement("div");
    el.className = "toast";
    el.textContent = text;
    document.getElementById("board-wrap").appendChild(el);
    setTimeout(function(){ if (el.parentNode) el.parentNode.removeChild(el); }, 3200);
  }

  // ---------- adjacency ----------
  function isAdjacent(a, b){
    var dr = Math.abs(a.row - b.row), dc = Math.abs(a.col - b.col);
    return Math.max(dr, dc) === 1;
  }
  function inChain(node){
    return chain.some(function(n){ return n.row === node.row && n.col === node.col; });
  }
  function sameAsIndex(node, idx){
    return chain[idx] && chain[idx].row === node.row && chain[idx].col === node.col;
  }
  function computeActiveType(chainArr){
    var active = null;
    for (var i = 0; i < chainArr.length; i++){
      active = (chainArr[i].type === "bus") ? null : chainArr[i].type;
    }
    return active;
  }

  // ---------- chain interaction ----------
  function nodeFromPoint(x, y){
    var el = document.elementFromPoint(x, y);
    if (!el) return null;
    var nodeEl = el.closest(".node");
    if (!nodeEl) return null;
    var row = parseInt(nodeEl.getAttribute("data-row"), 10);
    var col = parseInt(nodeEl.getAttribute("data-col"), 10);
    return { row: row, col: col, type: grid[row][col] };
  }

  function startChain(node){
    if (!running) return;
    playEnterSound();
    playSelectSound(1);
    chain = [node];
    dragging = true;
    busArmedFlashed = false;
    setSelected();
  }

  function extendChain(node){
    if (!dragging || !node) return;
    var last = chain[chain.length - 1];
    if (node.row === last.row && node.col === last.col) return;

    if (chain.length >= 2 && sameAsIndex(node, chain.length - 2)){
      chain.pop();
      playDeselectSound();
      setSelected();
      return;
    }
    if (inChain(node)) return;
    if (!isAdjacent(node, last)) return;

    if (node.type !== "bus"){
      var active = computeActiveType(chain);
      if (active !== null && node.type !== active) return;
    }

    chain.push(node);
    playSelectSound(chain.length);
    setSelected();

    if (chain.length === BUS_CHAIN_THRESHOLD && !busArmedFlashed){
      busArmedFlashed = true;
      toast("BUS OVERRIDE ARMED");
    }
  }

  function endChain(){
    if (!dragging) return;
    dragging = false;

    if (chain.length >= MIN_CHAIN){
      var pathSnapshot = chain.slice();
      resolveClear(chain.slice());
      animateAvatarPath(pathSnapshot);
    } else if (chain.length > 0){
      combo = 0;
      chain.forEach(function(n){
        var el = cellEl(n.row, n.col);
        if (el) el.classList.add("invalid");
      });
      setTimeout(function(){
        var all = nodesLayer.querySelectorAll(".node");
        all.forEach(function(el){ el.classList.remove("invalid","selected"); });
      }, 260);
    }
    chain = [];
    lineLayer.innerHTML = "";
    updateHud();
  }

  // ---------- trace ----------
  function hasBusOnBoard(){
    for (var r = 0; r < ROWS; r++)
      for (var c = 0; c < COLS; c++)
        if (grid[r][c] === "bus") return true;
    return false;
  }

  function applyTraceGain(gain){
    var prev = trace;
    trace = Math.min(100, trace + gain);
    maxTrace = Math.max(maxTrace, trace);

    if (trace >= 75 && prev < 75) toast("TRACE ESCALATION // SECURITY RESPONSE INCREASING");
    if (trace >= 90 && prev < 90){
      toast(objectiveComplete ? "CRITICAL TRACE // JACK OUT ADVISED" : "CRITICAL TRACE // OBJECTIVE INCOMPLETE, EXTRACTION LOCKED");
    }

    if (trace >= 100){
      dataLostToTrace += unbankedGB;
      unbankedGB = 0;
      updateHud();
      endRun("compromised");
      return;
    }
  }

  function handleJackOutClick(){
    playEnterSound();
    if (!objectiveComplete) { updateHud(); return; }
    if (unbankedGB <= 0){ toast("NOTHING ONBOARD TO BANK"); return; }
    var amount = +unbankedGB.toFixed(1);
    bankedGB += unbankedGB;
    unbankedGB = 0;
    trace = Math.max(0, trace - TRACE_JACKOUT_REDUCTION);
    extractionCount++;
    updateHud();
    toast("EXTRACTION SUCCESSFUL // BANKED " + amount + " GB");
  }

  // ---------- clearing / gravity ----------
  function resolveClear(nodes){
    var len = nodes.length;
    var basePoints = 0, gbGain = 0;
    nodes.forEach(function(n){
      basePoints += META[n.type].value;
      gbGain += META[n.type].gb;
    });
    gbGain = +gbGain.toFixed(1);

    var now = Date.now();
    if (now - lastClearTime < COMBO_WINDOW_MS) combo += 1;
    else combo = 1;
    lastClearTime = now;
    maxCombo = Math.max(maxCombo, combo);
    var comboMult = Math.min(combo, 8);

    var lengthBonus = 1 + Math.max(0, len - MIN_CHAIN) * 0.15;
    var points = Math.round(basePoints * lengthBonus * comboMult);

    score += points;
    unbankedGB += gbGain;
    chainLengths.push(len);
    nodes.forEach(function(n){ typeClearCounts[n.type] = (typeClearCounts[n.type] || 0) + 1; });
    var usedBus = nodes.some(function(n){ return n.type === "bus"; });
    if (usedBus) busOverridesUsedTotal++;

    floatText("+" + points, "points");
    if (comboMult > 1){
      var comboText = document.createElement("div");
      comboText.className = "floater combo";
      comboText.textContent = "×" + comboMult + " CHAIN LINK";
      feedbackEl.appendChild(comboText);
      setTimeout(function(){ if (comboText.parentNode) comboText.parentNode.removeChild(comboText); }, 900);
    }
    var dataText = document.createElement("div");
    dataText.className = "floater data";
    dataText.textContent = "+" + gbGain + " GB ONBOARD";
    feedbackEl.appendChild(dataText);
    setTimeout(function(){ if (dataText.parentNode) dataText.parentNode.removeChild(dataText); }, 900);

    var avgValue = basePoints / len;
    var traceGain = 0.6
      + Math.max(0, len - MIN_CHAIN) * 0.3
      + (avgValue / 13) * 1.4
      + (comboMult > 1 ? (comboMult - 1) * 0.3 : 0);
    if (trace >= 90) traceGain *= 1.5;
    else if (trace >= 75) traceGain *= 1.2;

    applyTraceGain(traceGain);
    if (!running) return;

    nodes.forEach(function(n){ grid[n.row][n.col] = null; });
    for (var c = 0; c < COLS; c++){
      var stack = [];
      for (var r = ROWS - 1; r >= 0; r--){
        if (grid[r][c] !== null) stack.push(grid[r][c]);
      }
      var newCol = [];
      for (var i = 0; i < ROWS - stack.length; i++) newCol.push(weightedType());
      newCol = newCol.concat(stack.slice().reverse());
      for (var r2 = 0; r2 < ROWS; r2++) grid[r2][c] = newCol[r2];
    }

    var spawnedBus = false;
    if (len >= BUS_CHAIN_THRESHOLD && !hasBusOnBoard()){
      var br = Math.floor(Math.random() * ROWS), bc = Math.floor(Math.random() * COLS);
      grid[br][bc] = "bus";
      spawnedBus = true;
    }

    render();
    updateHud();

    if (!objectiveComplete && (bankedGB + unbankedGB) >= TARGET_GB){
      objectiveComplete = true;
      objectiveCompletedAtElapsed = RUN_SECONDS - timeLeft;
      toast("OBJECTIVE COMPLETE — EXTRACTION AVAILABLE");
      updateHud();
    }
    if (spawnedBus){
      toast("SYSTEM BUS OVERRIDE GENERATED");
    }

    var hasEncrypted = nodes.some(function(n){ return n.type === "encrypted"; });
    if (hasEncrypted && !breachActive){
      startBreach();
    }
  }

  // ---------- breach terminal minigame ----------
  var breachSequence = [];
  var breachInput = [];
  var breachAcceptingInput = false;
  var breachCountdownHandle = null;
  var breachTimeoutHandle = null;
  var BREACH_TYPES = ["security","encrypted","system","power","crypto","schematic"];

  function shuffledTypes(){
    var arr = BREACH_TYPES.slice();
    for (var i = arr.length - 1; i > 0; i--){
      var j = Math.floor(Math.random() * (i + 1));
      var tmp = arr[i]; arr[i] = arr[j]; arr[j] = tmp;
    }
    return arr;
  }

  function startBreach(){
    breachActive = true;
    breachAcceptingInput = false;
    clearInterval(timerHandle);

    breachSequence = [];
    for (var i = 0; i < BREACH_SEQUENCE_LEN; i++){
      breachSequence.push(BREACH_TYPES[Math.floor(Math.random() * BREACH_TYPES.length)]);
    }
    breachInput = [];

    breachResultEl.textContent = "";
    breachResultEl.className = "breach-result";

    breachSlotsEl.innerHTML = "";
    for (var s = 0; s < BREACH_SEQUENCE_LEN; s++){
      var slot = document.createElement("div");
      slot.className = "breach-slot";
      slot.id = "breachSlot" + s;
      breachSlotsEl.appendChild(slot);
    }

    var keyOrder = shuffledTypes();
    breachKeysEl.innerHTML = "";
    keyOrder.forEach(function(t){
      var btn = document.createElement("div");
      btn.className = "breach-key";
      btn.setAttribute("data-type", t);
      btn.setAttribute("disabled", "true");
      btn.innerHTML = '<span class="glyph">' + META[t].glyph + '</span>';
      btn.addEventListener("click", function(){
        handleBreachTap(this.getAttribute("data-type"));
      });
      breachKeysEl.appendChild(btn);
    });

    breachOverlay.classList.remove("hidden");
    playBreachReveal();
  }

  function playBreachReveal(){
    var i = 0;
    function revealNext(){
      if (i >= breachSequence.length){
        setTimeout(beginBreachInput, 300);
        return;
      }
      var slot = document.getElementById("breachSlot" + i);
      if (slot){
        slot.classList.add("filled","reveal");
        slot.innerHTML = '<span class="glyph">' + META[breachSequence[i]].glyph + '</span>';
      }
      i++;
      setTimeout(revealNext, BREACH_REVEAL_MS);
    }
    revealNext();
  }

  function beginBreachInput(){
    for (var s = 0; s < BREACH_SEQUENCE_LEN; s++){
      var slot = document.getElementById("breachSlot" + s);
      if (slot){ slot.className = "breach-slot"; slot.innerHTML = ""; }
    }
    breachInput = [];
    breachAcceptingInput = true;
    breachKeysEl.querySelectorAll(".breach-key").forEach(function(btn){ btn.removeAttribute("disabled"); });

    var elapsed = 0;
    var stepMs = 90;
    breachTimerFill.style.width = "100%";
    breachCountdownHandle = setInterval(function(){
      elapsed += stepMs;
      var pct = Math.max(0, 100 - (elapsed / BREACH_TIME_LIMIT_MS) * 100);
      breachTimerFill.style.width = pct + "%";
    }, stepMs);
    breachTimeoutHandle = setTimeout(function(){
      if (breachAcceptingInput) breachFail("TIME EXPIRED");
    }, BREACH_TIME_LIMIT_MS);
  }

  function handleBreachTap(type){
    if (!breachAcceptingInput) return;
    playSelectSound(1);
    var idx = breachInput.length;
    var slot = document.getElementById("breachSlot" + idx);
    if (slot){
      slot.classList.add("filled");
      slot.innerHTML = '<span class="glyph">' + META[type].glyph + '</span>';
    }
    breachInput.push(type);

    if (type !== breachSequence[idx]){
      breachFail("CIPHER REJECTED");
      return;
    }
    if (breachInput.length === breachSequence.length){
      breachSuccess();
    }
  }

  function stopBreachTimers(){
    clearInterval(breachCountdownHandle);
    clearTimeout(breachTimeoutHandle);
  }

  function breachSuccess(){
    breachAcceptingInput = false;
    stopBreachTimers();
    playEnterSound();
    breachKeysEl.querySelectorAll(".breach-key").forEach(function(btn){ btn.setAttribute("disabled","true"); });
    unbankedGB += BREACH_SUCCESS_GB;
    score += BREACH_SUCCESS_SCORE;
    breachResultEl.textContent = "CIPHER CRACKED // +" + BREACH_SUCCESS_GB + " GB";
    breachResultEl.className = "breach-result success";
    updateHud();
    setTimeout(closeBreach, 1000);
  }

  function breachFail(reason){
    breachAcceptingInput = false;
    stopBreachTimers();
    playDeselectSound();
    breachKeysEl.querySelectorAll(".breach-key").forEach(function(btn){ btn.setAttribute("disabled","true"); });
    applyTraceGain(BREACH_FAIL_TRACE);
    breachResultEl.textContent = reason;
    breachResultEl.className = "breach-result fail";
    updateHud();
    setTimeout(closeBreach, 1000);
  }

  function closeBreach(){
    breachOverlay.classList.add("hidden");
    breachActive = false;
    stopBreachTimers();
    if (running){
      clearInterval(timerHandle);
      timerHandle = setInterval(tick, 1000);
    }
  }

  // ---------- pointer wiring ----------
  boardEl.addEventListener("pointerdown", function(e){
    var node = nodeFromPoint(e.clientX, e.clientY);
    if (node) startChain(node);
    e.preventDefault();
  });
  window.addEventListener("pointermove", function(e){
    if (!dragging) return;
    var node = nodeFromPoint(e.clientX, e.clientY);
    if (node) extendChain(node);
    e.preventDefault();
  }, { passive: false });
  window.addEventListener("pointerup", endChain);
  window.addEventListener("pointercancel", endChain);
  boardEl.addEventListener("touchmove", function(e){ e.preventDefault(); }, { passive: false });

  // ---------- timer / run lifecycle ----------
  function tick(){
    if (!running) return;
    timeLeft -= 1;
    updateHud();
    if (timeLeft <= 0){
      timeLeft = 0;
      updateHud();
      endRun("timeout");
    }
  }

  function classify(){
    var totalCleared = 0;
    for (var k in typeClearCounts) totalCleared += typeClearCounts[k];
    var avg = chainLengths.length ? (chainLengths.reduce(function(a,b){return a+b;},0) / chainLengths.length) : 0;
    var securityShare = typeClearCounts.security / Math.max(1, totalCleared);
    var fastCompletion = objectiveComplete && objectiveCompletedAtElapsed !== null &&
                          objectiveCompletedAtElapsed <= RUN_SECONDS * 0.45;
    var overstayed = dataLostToTrace > 0 || (bankedGB + unbankedGB) >= TARGET_GB * 1.5;

    if (avg >= 5.5 || busOverridesUsedTotal >= 2)
      return { tag:"ARCHITECT", desc:"elaborate, deliberate path construction" };
    if (securityShare >= 0.35)
      return { tag:"WRECKER", desc:"tore through defensive processes" };
    if (overstayed)
      return { tag:"GREEDY", desc:"stayed long after the job was done" };
    if (fastCompletion)
      return { tag:"SPEEDRUNNER", desc:"objective cleared with time to spare" };
    return { tag:"GHOST", desc:"minimal footprint, clean uplink" };
  }

  function endRun(reason){
    if (!running) return;
    running = false;
    clearInterval(timerHandle);
    stopHum();
    dragging = false; chain = [];

    if (reason === "abandoned"){
      dataLostToTrace += unbankedGB;
      unbankedGB = 0;
    }

    var avg = chainLengths.length ? (chainLengths.reduce(function(a,b){return a+b;},0) / chainLengths.length) : 0;
    var longest = chainLengths.length ? Math.max.apply(null, chainLengths) : 0;
    var cls = classify();

    var statusEl = document.getElementById("reportStatus");
    if (reason === "compromised"){
      statusEl.textContent = "CONNECTION COMPROMISED // UNBANKED DATA LOST";
      statusEl.classList.add("fail");
    } else if (reason === "abandoned"){
      statusEl.textContent = "RUN ABANDONED // UNBANKED DATA FORFEITED";
      statusEl.classList.add("fail");
    } else if (objectiveComplete){
      statusEl.textContent = "UPLINK CLOSED // OBJECTIVE COMPLETE";
      statusEl.classList.remove("fail");
    } else {
      statusEl.textContent = "UPLINK TIMED OUT // OBJECTIVE INCOMPLETE";
      statusEl.classList.add("fail");
    }

    document.getElementById("rBanked").textContent = Math.floor(bankedGB) + " GB";
    document.getElementById("rLost").textContent = Math.floor(dataLostToTrace) + " GB";
    document.getElementById("rExtractions").textContent = extractionCount;
    document.getElementById("rMaxTrace").textContent = Math.round(maxTrace) + "%";
    document.getElementById("rScore").textContent = score;
    document.getElementById("rLongest").textContent = longest;
    document.getElementById("rAvg").textContent = avg.toFixed(1);
    document.getElementById("rCombo").textContent = "×" + maxCombo;
    document.getElementById("rTag").textContent = cls.tag;
    document.getElementById("rTagDesc").textContent = cls.desc;

    summaryOverlay.classList.remove("hidden");
  }

  jackOutBtn.addEventListener("click", handleJackOutClick);

  abandonBtn.addEventListener("click", function(){
    if (!running) return;
    playDeselectSound();
    if (!abandonArmed){
      abandonArmed = true;
      abandonBtn.textContent = "TAP TO CONFIRM";
      abandonBtn.classList.add("urgent");
      clearTimeout(abandonArmTimeout);
      abandonArmTimeout = setTimeout(function(){
        abandonArmed = false;
        abandonBtn.textContent = "ABANDON";
        abandonBtn.classList.remove("urgent");
      }, 3000);
      return;
    }
    clearTimeout(abandonArmTimeout);
    abandonArmed = false;
    abandonBtn.textContent = "ABANDON";
    abandonBtn.classList.remove("urgent");
    endRun("abandoned");
  });
  reconnectBtn.addEventListener("click", function(){
    playEnterSound();
    resetRun();
  });

  startBtn.addEventListener("click", function(){
    playEnterSound();
    titleScreen.classList.add("hidden");
    resetRun();
  });

  profileBtn.addEventListener("click", function(){
    playEnterSound();
    profileOverlay.classList.remove("hidden");
  });

  saveProfileBtn.addEventListener("click", function(){
    playEnterSound();
    profileOverlay.classList.add("hidden");
  });

  window.addEventListener("resize", renderPathways);
  newGrid();
  render();
  renderPathways();
  placeAvatarInstant(START_ROW, START_COL);
  updateHud();
})();
