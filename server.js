"use strict";

/* ============================================================
 * UNO 派对桌 · Socket.io 服务端
 * ------------------------------------------------------------
 * 1. 所有房间与牌局状态都保存在服务端，客户端只负责渲染和发操作。
 * 2. 客户端通过 Socket.io 连接到本服务，由服务端中转全部消息，
 *    因此不同网络下的玩家只要都能访问本服务即可一起游玩，
 *    不要求处于同一个局域网 / 热点。
 * 3. 房主 / 客人只是权限标签（开始游戏、重新开局），牌局规则完全一致。
 * 4. 原有规则（+2/+4 叠加、功能牌、UNO 罚牌、自动洗牌、断线重连）
 *    与旧版浏览器权威逻辑保持一致。
 * ============================================================ */

const http = require("http");
const fs = require("fs");
const path = require("path");
const os = require("os");
const crypto = require("crypto");
const { Server } = require("socket.io");

const PORT = Number(process.env.PORT) || 3000;
const HOST = process.env.HOST || "0.0.0.0";

const PROTOCOL = 1;
const COLORS = ["red", "yellow", "green", "blue"];
const COLOR_NAMES = {
  red: "红色",
  yellow: "黄色",
  green: "绿色",
  blue: "蓝色",
};
const VULNERABILITY_MS = 5000;
const ROOM_IDLE_MS = 1000 * 60 * 30; // 全员离线 30 分钟后回收房间
const MAX_PLAYERS = 4;

/* ============================================================
 * 一、通用工具
 * ============================================================ */
function randomInt(max) {
  if (!Number.isFinite(max) || max <= 0) return 0;
  return crypto.randomInt(max);
}

function randomCode() {
  return String(100000 + randomInt(900000));
}

function randomId(prefix = "id") {
  const bytes = crypto.randomBytes(10);
  const raw = Array.from(bytes, (b) => (b % 36).toString(36)).join("");
  return `${prefix}_${raw}`;
}

function normalizeName(value) {
  return String(value || "")
    .replace(/[\u0000-\u001f\u007f]/g, "")
    .replace(/\s+/g, " ")
    .trim()
    .slice(0, 12);
}

function normalizeCode(value) {
  return String(value || "")
    .replace(/\D/g, "")
    .slice(0, 6);
}

function isValidCode(code) {
  return /^\d{6}$/.test(String(code || ""));
}

function freshStats() {
  return { played: 0, drawn: 0, penalty: 0, unoCalls: 0, catches: 0 };
}

function playerStatsView(player) {
  return { ...(player.stats || freshStats()) };
}

function playerById(room, id) {
  return room?.players?.find((p) => p.id === id) || null;
}

function nextPlayerId(room, fromId, steps = 1) {
  if (!room || !room.players.length) return null;
  const index = room.players.findIndex((p) => p.id === fromId);
  if (index < 0) return room.players[0].id;
  const n = room.players.length;
  const direction = room.direction === -1 ? -1 : 1;
  const nextIndex = (((index + direction * steps) % n) + n) % n;
  return room.players[nextIndex].id;
}

/* 客户端同样使用这套判断，用于高亮“当前可出的牌”；服务端才是最终裁决 */
function isCardPlayable(card, context) {
  if (!card || !context || !context.topCard) return false;
  if (Number(context.pendingDraw) > 0) {
    return card.value === "draw2" || card.value === "wild4";
  }
  if (card.color === "black") return true;
  return (
    card.color === context.activeColor || card.value === context.topCard.value
  );
}

function hasStackCard(player) {
  return !!player?.hand?.some(
    (card) => card.value === "draw2" || card.value === "wild4",
  );
}

function makeDeck() {
  const deck = [];
  let n = 0;
  const add = (color, value) => {
    deck.push({ id: `${color}-${value}-${n++}`, color, value });
  };
  COLORS.forEach((color) => {
    add(color, "0");
    for (let i = 1; i <= 9; i += 1) {
      add(color, String(i));
      add(color, String(i));
    }
    ["skip", "reverse", "draw2"].forEach((value) => {
      add(color, value);
      add(color, value);
    });
  });
  ["wild", "wild4"].forEach((value) => {
    for (let i = 0; i < 4; i += 1) add("black", value);
  });
  return deck;
}

function shuffleArray(source) {
  const arr = source.slice();
  for (let i = arr.length - 1; i > 0; i -= 1) {
    const j = randomInt(i + 1);
    [arr[i], arr[j]] = [arr[j], arr[i]];
  }
  return arr;
}

class GameError extends Error {
  constructor(message) {
    super(message);
    this.name = "GameError";
  }
}

/* ============================================================
 * 二、房间（牌局权威状态）
 * ============================================================ */
class HostRoom {
  constructor({ code, hostName, hostToken }) {
    this.autoPenaltyTimer = null;
    this.autoEndTimer = null;
    this.lastActivity = Date.now();

    this.room = {
      v: PROTOCOL,
      code,
      phase: "lobby",
      players: [],
      currentPlayerId: null,
      direction: 1,
      drawPile: [],
      discardPile: [],
      topCard: null,
      activeColor: null,
      pendingDraw: 0,
      stackTrail: [],
      hasDrawnThisTurn: false,
      drawnCardId: null,
      unoVulnerabilities: [],
      winnerId: null,
      paused: false,
      startedAt: 0,
      endedAt: 0,
      createdAt: Date.now(),
      version: 0,
      eventSeq: 0,
      lastEvent: null,
    };

    const host = {
      id: randomId("host"),
      token: hostToken || randomId("token"),
      name: normalizeName(hostName) || "房主",
      isHost: true,
      connected: false,
      socketId: null,
      hand: [],
      unoArmed: false,
      stats: freshStats(),
    };
    this.room.players.push(host);
    this.hostPlayerId = host.id;
  }

  get players() {
    return this.room.players;
  }

  get hostPlayer() {
    return playerById(this.room, this.hostPlayerId);
  }

  playerByToken(token) {
    return this.room.players.find((p) => p.token === token) || null;
  }

  touch() {
    this.lastActivity = Date.now();
  }

  addPlayer(name, token) {
    if (this.room.phase !== "lobby") {
      throw new GameError("牌局已经开始，无法中途加入");
    }
    if (this.room.players.length >= MAX_PLAYERS) {
      throw new GameError("房间已满（最多 4 人）");
    }
    const clean = normalizeName(name);
    if (!clean) throw new GameError("请输入昵称");
    if (
      this.room.players.some((p) => p.name.toLowerCase() === clean.toLowerCase())
    ) {
      throw new GameError("房间里已经有同名玩家，请换一个昵称");
    }
    const conflict = this.playerByToken(token);
    if (conflict) return conflict;

    const player = {
      id: randomId("guest"),
      token: token || randomId("token"),
      name: clean,
      isHost: false,
      connected: false,
      socketId: null,
      hand: [],
      unoArmed: false,
      stats: freshStats(),
    };
    this.room.players.push(player);
    return player;
  }

  removeLobbyPlayer(playerId) {
    if (this.room.phase !== "lobby") return false;
    const index = this.room.players.findIndex(
      (p) => p.id === playerId && !p.isHost,
    );
    if (index < 0) return false;
    this.room.players.splice(index, 1);
    this.bumpPresence();
    return true;
  }

  removeOfflineLobbyPlayer(requesterId, targetId) {
    const requester = playerById(this.room, requesterId);
    if (!requester?.isHost) throw new GameError("只有房主可以移除玩家");
    if (this.room.phase !== "lobby") {
      throw new GameError("牌局进行中不能移除玩家");
    }
    const target = playerById(this.room, targetId);
    if (!target || target.isHost) throw new GameError("无法移除该玩家");
    if (target.connected) throw new GameError("只能移除已经离线的玩家");
    this.room.players.splice(this.room.players.indexOf(target), 1);
    this.bumpPresence();
    return target;
  }

  recalculatePause() {
    const r = this.room;
    if (r.phase === "playing") {
      r.paused = r.players.some((p) => !p.connected);
    } else {
      r.paused = false;
    }
    if (r.paused) this.clearAutoTimers();
  }

  bumpPresence() {
    this.room.version += 1;
    this.recalculatePause();
    this.pruneVulnerabilities();
    if (!this.room.paused) {
      this.scheduleAutoPenalty();
      this.scheduleAutoEndIfNeeded();
    } else {
      this.clearAutoTimers();
    }
    this.touch();
    broadcastRoom(this);
  }

  emit(event) {
    this.room.version += 1;
    if (event) {
      this.room.eventSeq += 1;
      this.room.lastEvent = {
        ...event,
        seq: this.room.eventSeq,
        at: Date.now(),
      };
    }
    this.recalculatePause();
    this.pruneVulnerabilities();
    if (!this.room.paused) {
      this.scheduleAutoPenalty();
      this.scheduleAutoEndIfNeeded();
    } else {
      this.clearAutoTimers();
    }
    this.touch();
    broadcastRoom(this);
  }

  clearAutoTimers() {
    if (this.autoPenaltyTimer) {
      clearTimeout(this.autoPenaltyTimer);
      this.autoPenaltyTimer = null;
    }
    if (this.autoEndTimer) {
      clearTimeout(this.autoEndTimer);
      this.autoEndTimer = null;
    }
  }

  scheduleAutoPenalty() {
    if (this.autoPenaltyTimer) {
      clearTimeout(this.autoPenaltyTimer);
      this.autoPenaltyTimer = null;
    }
    const r = this.room;
    if (r.phase !== "playing" || r.paused || r.pendingDraw <= 0) return;
    const current = playerById(r, r.currentPlayerId);
    if (!current || !current.connected || hasStackCard(current)) return;
    const version = r.version;
    const targetId = current.id;
    this.autoPenaltyTimer = setTimeout(() => {
      this.autoPenaltyTimer = null;
      if (
        this.room.version !== version ||
        this.room.paused ||
        this.room.phase !== "playing"
      )
        return;
      if (this.room.currentPlayerId !== targetId || this.room.pendingDraw <= 0)
        return;
      try {
        this.acceptPenalty(targetId, true);
      } catch (_) {
        /* 状态已经改变时让下一次状态更新重新调度 */
      }
    }, 1250);
  }

  scheduleAutoEndIfNeeded() {
    if (this.autoEndTimer) {
      clearTimeout(this.autoEndTimer);
      this.autoEndTimer = null;
    }
    const r = this.room;
    if (r.phase !== "playing" || r.paused || !r.hasDrawnThisTurn) return;
    const current = playerById(r, r.currentPlayerId);
    if (!current || !current.connected) return;
    const drawn = current.hand.find((c) => c.id === r.drawnCardId) || null;
    if (drawn && isCardPlayable(drawn, r)) return;
    const version = r.version;
    const targetId = current.id;
    this.autoEndTimer = setTimeout(() => {
      this.autoEndTimer = null;
      if (
        this.room.version !== version ||
        this.room.paused ||
        this.room.phase !== "playing"
      )
        return;
      if (
        this.room.currentPlayerId !== targetId ||
        !this.room.hasDrawnThisTurn
      )
        return;
      try {
        this.endTurn(targetId, true);
      } catch (_) {
        /* 忽略已经过期的自动结束 */
      }
    }, 1000);
  }

  pruneVulnerabilities() {
    const now = Date.now();
    if (!Array.isArray(this.room.unoVulnerabilities)) {
      this.room.unoVulnerabilities = [];
      return;
    }
    this.room.unoVulnerabilities = this.room.unoVulnerabilities.filter((v) => {
      if (v.expiresAt <= now) return false;
      // 只要目标不再只剩 1 张（摸牌 / 被抓 / 受罚），抓 UNO 窗口立即失效
      const player = playerById(this.room, v.playerId);
      return !!player && player.hand.length === 1;
    });
  }

  addVulnerability(playerId) {
    this.pruneVulnerabilities();
    this.room.unoVulnerabilities = this.room.unoVulnerabilities.filter(
      (v) => v.playerId !== playerId,
    );
    this.room.unoVulnerabilities.push({
      id: randomId("vuln"),
      playerId,
      expiresAt: Date.now() + VULNERABILITY_MS,
    });
  }

  ensureDrawPile() {
    const r = this.room;
    if (r.drawPile.length > 0) return false;
    if (r.discardPile.length <= 1) return false;
    const top = r.discardPile[r.discardPile.length - 1];
    const recyclable = r.discardPile.slice(0, -1);
    r.drawPile = shuffleArray(recyclable);
    r.discardPile = [top];
    return true;
  }

  drawCards(player, count, { penalty = false } = {}) {
    const cards = [];
    let reshuffled = false;
    for (let i = 0; i < count; i += 1) {
      if (this.room.drawPile.length === 0) {
        const didReshuffle = this.ensureDrawPile();
        if (didReshuffle) reshuffled = true;
      }
      if (this.room.drawPile.length === 0) break;
      const card = this.room.drawPile.pop();
      player.hand.push(card);
      player.stats.drawn += 1;
      if (penalty) player.stats.penalty += 1;
      cards.push(card);
    }
    return { cards, reshuffled };
  }

  startGame(requesterId) {
    const host = playerById(this.room, requesterId);
    if (!host?.isHost) throw new GameError("只有房主可以开始游戏");
    if (this.room.players.length < 2) {
      throw new GameError("至少需要 2 名真人玩家");
    }
    if (this.room.players.length > MAX_PLAYERS) {
      throw new GameError("最多 4 名玩家");
    }
    if (this.room.players.some((p) => !p.connected)) {
      throw new GameError("有玩家尚未连回牌桌，请等待所有人上线");
    }

    this.clearAutoTimers();
    const r = this.room;
    r.phase = "playing";
    r.paused = false;
    r.direction = 1;
    r.currentPlayerId = null;
    r.drawPile = shuffleArray(makeDeck());
    r.discardPile = [];
    r.topCard = null;
    r.activeColor = null;
    r.pendingDraw = 0;
    r.stackTrail = [];
    r.hasDrawnThisTurn = false;
    r.drawnCardId = null;
    r.unoVulnerabilities = [];
    r.winnerId = null;
    r.startedAt = Date.now();
    r.endedAt = 0;
    r.players.forEach((p) => {
      p.hand = [];
      p.unoArmed = false;
      p.stats = freshStats();
    });

    // 轮流发 5 张
    for (let round = 0; round < 5; round += 1) {
      r.players.forEach((p) => {
        p.hand.push(r.drawPile.pop());
      });
    }

    // 起始牌不能是变色 / +4；黑牌放回牌堆底部继续找
    let guard = 0;
    while (r.drawPile.length && guard < 200) {
      guard += 1;
      const candidate = r.drawPile.pop();
      if (candidate.value !== "wild" && candidate.value !== "wild4") {
        r.discardPile.push(candidate);
        r.topCard = candidate;
        r.activeColor = candidate.color;
        break;
      }
      r.drawPile.unshift(candidate);
    }
    if (!r.topCard) throw new GameError("无法生成起始牌，请重试");

    // 改动 6：发牌结束后随机决定先手（不再固定房主先手）
    const starterIndex = randomInt(r.players.length);
    const starter = r.players[starterIndex];
    r.currentPlayerId = starter.id;

    let initialEffect = "none";
    let initialTargetId = starter.id;
    let initialDraw = 0;
    let skippedId = null;
    let reshuffled = false;

    if (r.topCard.value === "skip") {
      initialEffect = "skip";
      skippedId = starter.id;
      initialTargetId = starter.id;
      r.currentPlayerId = nextPlayerId(r, starter.id, 1);
    } else if (r.topCard.value === "reverse") {
      initialEffect = "reverse";
      r.direction = -1;
      if (r.players.length === 2) {
        // 2 人局反转视同跳过：被指定先手的人失去这一回合
        skippedId = starter.id;
        initialTargetId = starter.id;
        r.currentPlayerId = nextPlayerId(r, starter.id, 1);
      } else {
        r.currentPlayerId = starter.id;
      }
    } else if (r.topCard.value === "draw2") {
      initialEffect = "draw2";
      initialTargetId = starter.id;
      const drawRes = this.drawCards(starter, 2, { penalty: true });
      initialDraw = drawRes.cards.length;
      reshuffled = drawRes.reshuffled;
      skippedId = starter.id;
      r.currentPlayerId = nextPlayerId(r, starter.id, 1);
    }

    this.emit({
      type: "start",
      starterId: r.currentPlayerId,
      initialEffect,
      initialTargetId,
      initialDraw,
      skippedId,
      reshuffled,
      card: r.topCard,
      direction: r.direction,
    });
  }

  handleAction(playerId, action) {
    const player = playerById(this.room, playerId);
    if (!player) throw new GameError("你不在这个房间里");
    if (!action || typeof action !== "object" || !action.type) {
      throw new GameError("无效操作");
    }
    switch (action.type) {
      case "start-game":
        this.startGame(playerId);
        return;
      case "restart-game":
        if (!player.isHost) throw new GameError("只有房主可以重新开局");
        this.startGame(playerId);
        return;
      case "play":
        this.playCard(playerId, action.cardId, action.color);
        return;
      case "draw":
        this.drawAction(playerId);
        return;
      case "end-turn":
        this.endTurn(playerId, false);
        return;
      case "uno":
        this.declareUno(playerId);
        return;
      case "catch-uno":
        this.catchUno(playerId, action.targetId);
        return;
      case "remove-offline":
        this.removeOfflineLobbyPlayer(playerId, action.targetId);
        return;
      default:
        throw new GameError("无效操作");
    }
  }

  assertCanAct(playerId) {
    const r = this.room;
    if (r.phase !== "playing") throw new GameError("牌局还没有开始");
    if (r.paused) throw new GameError("牌局暂停中，等待玩家重连");
    if (r.currentPlayerId !== playerId) throw new GameError("还没轮到你");
  }

  playCard(playerId, cardId, color) {
    this.assertCanAct(playerId);
    const r = this.room;
    const player = playerById(r, playerId);
    const index = player.hand.findIndex((c) => c.id === cardId);
    if (index < 0) throw new GameError("这张牌已经不在手里了");
    const card = player.hand[index];

    if (r.hasDrawnThisTurn && r.drawnCardId !== card.id) {
      throw new GameError("抽牌后只能打出刚抽到的那张牌");
    }
    if (r.pendingDraw > 0) {
      if (card.value !== "draw2" && card.value !== "wild4") {
        throw new GameError("叠加中只能打出 +2 或 +4");
      }
    } else if (!isCardPlayable(card, r)) {
      throw new GameError("这张牌和顶牌不匹配");
    }

    let chosenColor = null;
    if (card.value === "wild" || card.value === "wild4") {
      if (!COLORS.includes(color)) {
        throw new GameError("请为万能牌选择一个颜色");
      }
      chosenColor = color;
    }

    const wasStack = r.pendingDraw > 0;
    player.hand.splice(index, 1);
    r.discardPile.push(card);
    r.topCard = card;
    r.activeColor = chosenColor || card.color;
    r.hasDrawnThisTurn = false;
    r.drawnCardId = null;
    player.stats.played += 1;

    // 先检查胜利：出完最后一张即结束，后续牌效不再处理
    if (player.hand.length === 0) {
      this.clearAutoTimers();
      r.winnerId = player.id;
      r.phase = "ended";
      r.paused = false;
      r.endedAt = Date.now();
      r.pendingDraw = 0;
      r.stackTrail = [];
      r.unoVulnerabilities = [];
      player.unoArmed = false;
      this.emit({
        type: "win",
        actorId: player.id,
        winnerId: player.id,
        card,
        color: r.activeColor,
        direction: r.direction,
      });
      return;
    }

    let unoDeclared = false;
    let unoVulnerable = false;
    if (player.hand.length === 1) {
      if (player.unoArmed) {
        player.unoArmed = false;
        player.stats.unoCalls += 1;
        unoDeclared = true;
      } else {
        this.addVulnerability(player.id);
        unoVulnerable = true;
      }
    } else {
      player.unoArmed = false;
    }

    let skippedId = null;
    if (card.value === "skip") {
      skippedId = nextPlayerId(r, player.id, 1);
      r.currentPlayerId = nextPlayerId(r, player.id, 2);
    } else if (card.value === "reverse") {
      r.direction = r.direction === 1 ? -1 : 1;
      if (r.players.length === 2) {
        // 2 人局反转等同跳过，当前玩家继续
        r.currentPlayerId = player.id;
      } else {
        r.currentPlayerId = nextPlayerId(r, player.id, 1);
      }
    } else if (card.value === "draw2" || card.value === "wild4") {
      const amount = card.value === "draw2" ? 2 : 4;
      r.pendingDraw += amount;
      const targetId = nextPlayerId(r, player.id, 1);
      r.stackTrail.push({
        playerId: player.id,
        targetId,
        amount,
        total: r.pendingDraw,
        cardValue: card.value,
      });
      r.currentPlayerId = targetId;
    } else {
      r.currentPlayerId = nextPlayerId(r, player.id, 1);
    }

    this.emit({
      type: "play",
      actorId: player.id,
      card,
      color: r.activeColor,
      chosenColor,
      direction: r.direction,
      pendingDraw: r.pendingDraw,
      stackTrail: r.stackTrail.slice(-8),
      stacked: wasStack,
      targetId: r.currentPlayerId,
      skippedId,
      unoDeclared,
      unoVulnerable,
      handCount: player.hand.length,
    });
  }

  /**
   * 改动 3：UNO 按钮在“手里只剩 1 张且还没喊”时提醒。
   * - 手牌 2 张：保留旧版“提前喊”，出牌后自动生效；
   * - 手牌 1 张：视为 5 秒窗口内的补喊，清除自己的被抓窗口。
   */
  declareUno(playerId) {
    const r = this.room;
    if (r.phase !== "playing") throw new GameError("牌局还没有开始");
    if (r.paused) throw new GameError("牌局暂停中，等待玩家重连");
    const player = playerById(r, playerId);
    if (!player) throw new GameError("你不在这个房间里");
    if (player.unoArmed) throw new GameError("你已经喊过 UNO 了");
    if (player.hand.length !== 1 && player.hand.length !== 2) {
      throw new GameError("只有手牌剩 1 ~ 2 张时才能喊 UNO");
    }
    if (player.hand.length === 1) {
      // 补喊：撤销自己的 UNO 漏洞，其他人不能再抓
      r.unoVulnerabilities = r.unoVulnerabilities.filter(
        (v) => v.playerId !== playerId,
      );
    }
    player.unoArmed = true;
    player.stats.unoCalls += 1;
    this.emit({ type: "uno", playerId, kind: "declared", late: true });
  }

  catchUno(catcherId, targetId) {
    const r = this.room;
    if (r.phase !== "playing") throw new GameError("牌局还没有开始");
    if (r.paused) throw new GameError("牌局暂停中，等待玩家重连");
    if (catcherId === targetId) throw new GameError("不能抓自己");
    const catcher = playerById(r, catcherId);
    const victim = playerById(r, targetId);
    if (!catcher || !victim) throw new GameError("玩家不存在");
    if (victim.hand.length !== 1) {
      throw new GameError("对方已经不是最后一张手牌了");
    }
    const index = r.unoVulnerabilities.findIndex(
      (v) => v.playerId === targetId,
    );
    if (index < 0) throw new GameError("没有可抓的 UNO");
    const vuln = r.unoVulnerabilities[index];
    if (Date.now() > vuln.expiresAt) {
      r.unoVulnerabilities.splice(index, 1);
      throw new GameError("抓晚了，已经超过 5 秒");
    }
    r.unoVulnerabilities.splice(index, 1);
    const drawRes = this.drawCards(victim, 2, { penalty: true });
    catcher.stats.catches += 1;
    this.emit({
      type: "catch",
      catcherId,
      victimId: targetId,
      amount: 2,
      drawn: drawRes.cards.length,
      reshuffled: drawRes.reshuffled,
      direction: r.direction,
    });
  }

  drawAction(playerId) {
    this.assertCanAct(playerId);
    const r = this.room;
    if (r.pendingDraw > 0) {
      this.acceptPenalty(playerId, false);
      return;
    }
    if (r.hasDrawnThisTurn) throw new GameError("这个回合已经抽过牌了");
    const player = playerById(r, playerId);
    const drawRes = this.drawCards(player, 1, { penalty: false });
    const card = drawRes.cards[0] || null;
    r.hasDrawnThisTurn = true;
    r.drawnCardId = card?.id || null;
    player.unoArmed = false;
    this.emit({
      type: "draw",
      playerId,
      count: drawRes.cards.length,
      reshuffled: drawRes.reshuffled,
      handCount: player.hand.length,
      direction: r.direction,
    });
  }

  acceptPenalty(playerId, auto = false) {
    if (this.room.phase !== "playing") {
      throw new GameError("牌局还没有开始");
    }
    if (this.room.paused) throw new GameError("牌局暂停中");
    if (this.room.currentPlayerId !== playerId) {
      throw new GameError("还没轮到你");
    }
    const r = this.room;
    const amount = r.pendingDraw;
    if (amount <= 0) throw new GameError("当前没有累计罚牌");
    const player = playerById(r, playerId);
    const totalBefore = amount;
    const drawRes = this.drawCards(player, amount, { penalty: true });
    r.unoVulnerabilities = r.unoVulnerabilities.filter(
      (v) => v.playerId !== playerId,
    );
    player.unoArmed = false;
    r.pendingDraw = 0;
    r.stackTrail = [];
    r.hasDrawnThisTurn = false;
    r.drawnCardId = null;
    r.currentPlayerId = nextPlayerId(r, playerId, 1);
    this.emit({
      type: "penalty",
      playerId,
      totalBefore,
      amount,
      drawn: drawRes.cards.length,
      reshuffled: drawRes.reshuffled,
      auto: !!auto,
      direction: r.direction,
    });
  }

  endTurn(playerId, auto = false) {
    this.assertCanAct(playerId);
    const r = this.room;
    if (!r.hasDrawnThisTurn) {
      throw new GameError("还没有抽牌，不能结束回合");
    }
    const player = playerById(r, playerId);
    player.unoArmed = false;
    r.hasDrawnThisTurn = false;
    r.drawnCardId = null;
    r.currentPlayerId = nextPlayerId(r, playerId, 1);
    this.emit({
      type: "end-turn",
      playerId,
      auto: !!auto,
      direction: r.direction,
    });
  }

  /** 按玩家生成私有视图：别人的手牌不会泄露，只给数量 */
  buildView(forPlayerId) {
    this.pruneVulnerabilities();
    const r = this.room;
    const me = playerById(r, forPlayerId);
    const now = Date.now();
    return {
      protocol: PROTOCOL,
      version: r.version,
      code: r.code,
      selfId: forPlayerId,
      phase: r.phase,
      players: r.players.map((p) => ({
        id: p.id,
        name: p.name,
        isHost: !!p.isHost,
        connected: !!p.connected,
        handCount: p.hand.length,
        unoArmed: !!p.unoArmed,
        stats: playerStatsView(p),
      })),
      currentPlayerId: r.currentPlayerId,
      direction: r.direction,
      topCard: r.topCard,
      activeColor: r.activeColor,
      drawPileCount: r.drawPile.length,
      discardCount: r.discardPile.length,
      pendingDraw: r.pendingDraw,
      stackTrail: r.stackTrail.slice(-8).map((item) => ({ ...item })),
      hasDrawnThisTurn: !!r.hasDrawnThisTurn,
      // 刚抽到的牌只对自己的视图可见
      drawnCardId: forPlayerId === r.currentPlayerId ? r.drawnCardId : null,
      hand: (me?.hand || []).map((c) => ({ ...c })),
      unoVulnerabilities: r.unoVulnerabilities
        .filter((v) => v.expiresAt > now)
        .map((v) => ({
          playerId: v.playerId,
          remainingMs: Math.max(0, v.expiresAt - now),
        })),
      winnerId: r.winnerId,
      paused: !!r.paused,
      pauseNames: r.players.filter((p) => !p.connected).map((p) => p.name),
      startedAt: r.startedAt,
      endedAt: r.endedAt,
      createdAt: r.createdAt,
      lastEvent: r.lastEvent,
      hostId: this.hostPlayerId,
      serverNow: now,
    };
  }

  markOffline() {
    this.recalculatePause();
    this.pruneVulnerabilities();
    if (!this.room.paused) {
      this.scheduleAutoPenalty();
      this.scheduleAutoEndIfNeeded();
    } else {
      this.clearAutoTimers();
    }
    this.touch();
    broadcastRoom(this);
  }
}

/* ============================================================
 * 三、HTTP 静态资源 + Socket.io 服务
 * ============================================================ */
const MIME_TYPES = {
  ".html": "text/html; charset=utf-8",
  ".js": "text/javascript; charset=utf-8",
  ".css": "text/css; charset=utf-8",
  ".json": "application/json; charset=utf-8",
  ".png": "image/png",
  ".jpg": "image/jpeg",
  ".jpeg": "image/jpeg",
  ".svg": "image/svg+xml",
  ".ico": "image/x-icon",
  ".webp": "image/webp",
};

const httpServer = http.createServer((req, res) => {
  let pathname = "/";
  try {
    pathname = decodeURIComponent(
      new URL(req.url, "http://localhost").pathname,
    );
  } catch (_) {
    res.writeHead(400, { "Content-Type": "text/plain; charset=utf-8" });
    res.end("Bad Request");
    return;
  }

  if (pathname === "/") pathname = "/index.html";
  if (pathname === "/healthz") {
    res.writeHead(200, { "Content-Type": "text/plain; charset=utf-8" });
    res.end("ok");
    return;
  }

  const filePath = path.normalize(path.join(__dirname, pathname));
  if (filePath !== __dirname && !filePath.startsWith(__dirname + path.sep)) {
    res.writeHead(403, { "Content-Type": "text/plain; charset=utf-8" });
    res.end("Forbidden");
    return;
  }

  // 只暴露页面和图片资源，避免把 server.js / package.json / node_modules 发出去
  const relPath = path.relative(__dirname, filePath).split(path.sep).join("/");
  if (relPath !== "index.html" && !relPath.startsWith("img/")) {
    res.writeHead(404, { "Content-Type": "text/plain; charset=utf-8" });
    res.end("Not Found");
    return;
  }

  fs.stat(filePath, (err, stat) => {
    if (err || !stat.isFile()) {
      res.writeHead(404, { "Content-Type": "text/plain; charset=utf-8" });
      res.end("Not Found");
      return;
    }
    const ext = path.extname(filePath).toLowerCase();
    const headers = {
      "Content-Type": MIME_TYPES[ext] || "application/octet-stream",
      "X-Content-Type-Options": "nosniff",
      "Cache-Control":
        ext === ".html" ? "no-cache, no-store, must-revalidate" : "public, max-age=3600",
    };
    res.writeHead(200, headers);
    const stream = fs.createReadStream(filePath);
    stream.on("error", () => {
      if (!res.headersSent) res.writeHead(500);
      res.end();
    });
    stream.pipe(res);
  });
});

const io = new Server(httpServer, {
  maxHttpBufferSize: 1e6,
  pingInterval: 20000,
  pingTimeout: 20000,
  cors: { origin: "*" },
});

const rooms = new Map();

function broadcastRoom(hostRoom) {
  if (!hostRoom) return;
  hostRoom.room.players.forEach((player) => {
    if (!player.socketId || !player.connected) return;
    const socket = io.sockets.sockets.get(player.socketId);
    if (!socket) return;
    socket.emit("state", hostRoom.buildView(player.id));
  });
}

function roomNotice(code, message, type = "info") {
  if (!code || !message) return;
  io.to(code).emit("notice", { message, type });
}

function attachSocketToPlayer(socket, room, player) {
  const oldSocketId = player.socketId;
  const wasOffline = !player.connected;

  // 先绑定新连接，再踢掉旧连接，旧连接的 disconnect 会因 socketId 不匹配而忽略
  player.socketId = socket.id;
  player.connected = true;
  socket.data.code = room.room.code;
  socket.data.playerId = player.id;
  socket.join(room.room.code);

  if (oldSocketId && oldSocketId !== socket.id) {
    const oldSocket = io.sockets.sockets.get(oldSocketId);
    if (oldSocket) {
      oldSocket.emit("kicked", {
        message: "这个座位已经在另一个窗口上线，本窗口已断开。",
      });
      oldSocket.disconnect(true);
    }
  }
  return wasOffline;
}

function failJoin(socket, message) {
  socket.emit("join-error", { message });
}

io.on("connection", (socket) => {
  socket.data.code = null;
  socket.data.playerId = null;

  /* ---------- 创建房间 ---------- */
  socket.on("create-room", (payload) => {
    try {
      // 幂等处理：客户端入场请求带自动补发，若第一次已创建成功但回包丢失，
      // 这里直接把已有房间的 joined 再发一次，而不是误报“已经在房间里”。
      if (socket.data.code) {
        const existing = rooms.get(socket.data.code);
        const existingPlayer = playerById(existing?.room, socket.data.playerId);
        if (existing && existingPlayer) {
          socket.emit("joined", {
            protocol: PROTOCOL,
            playerId: existingPlayer.id,
            code: existing.room.code,
            isHost: !!existingPlayer.isHost,
            view: existing.buildView(existingPlayer.id),
          });
          return;
        }
        socket.data.code = null;
        socket.data.playerId = null;
      }
      if (payload?.v && Number(payload.v) !== PROTOCOL) {
        failJoin(socket, "客户端版本不一致，请刷新页面后再试。");
        return;
      }
      const name = normalizeName(payload?.name);
      const token = String(payload?.token || "").slice(0, 100);
      if (!name) {
        failJoin(socket, "请输入昵称后再创建房间。");
        return;
      }
      if (!token) {
        failJoin(socket, "缺少玩家身份凭据，请刷新页面后重试。");
        return;
      }

      let code = "";
      for (let i = 0; i < 20; i += 1) {
        code = randomCode();
        if (!rooms.has(code)) break;
      }
      if (!code || rooms.has(code)) {
        failJoin(socket, "房间码连续被占用，请稍后重试。");
        return;
      }

      const room = new HostRoom({ code, hostName: name, hostToken: token });
      rooms.set(code, room);
      const host = room.hostPlayer;
      attachSocketToPlayer(socket, room, host);

      socket.emit("joined", {
        protocol: PROTOCOL,
        playerId: host.id,
        code,
        isHost: true,
        view: room.buildView(host.id),
      });
      room.bumpPresence();
      console.log(`[房间] ${code} 创建 · 房主 ${host.name}`);
    } catch (error) {
      failJoin(
        socket,
        error instanceof GameError ? error.message : "创建房间失败，请重试。",
      );
    }
  });

  /* ---------- 加入 / 重连房间 ---------- */
  socket.on("join-room", (payload) => {
    try {
      if (payload?.v && Number(payload.v) !== PROTOCOL) {
        failJoin(socket, "客户端版本不一致，请刷新页面后再试。");
        return;
      }
      const code = normalizeCode(payload?.code);
      const name = normalizeName(payload?.name);
      const token = String(payload?.token || "").slice(0, 100);
      if (!isValidCode(code)) {
        failJoin(socket, "房间码格式不正确，请输入 6 位数字。");
        return;
      }
      if (!name) {
        failJoin(socket, "请先输入昵称。");
        return;
      }
      if (!token) {
        failJoin(socket, "缺少玩家身份凭据，请刷新页面后重试。");
        return;
      }

      const room = rooms.get(code);
      if (!room) {
        failJoin(socket, "找不到这个房间：房间码不正确，或房间已经关闭。");
        return;
      }

      // 如果这个 socket 之前绑在别的房间，先把旧座位标记为离线再解绑
      if (socket.data.code && socket.data.code !== code) {
        const oldCode = socket.data.code;
        const oldRoom = rooms.get(oldCode);
        const oldPlayer = playerById(oldRoom?.room, socket.data.playerId);
        if (oldRoom && oldPlayer && oldPlayer.socketId === socket.id) {
          oldPlayer.socketId = null;
          oldPlayer.connected = false;
          oldRoom.markOffline();
          roomNotice(oldCode, `${oldPlayer.name} 离开了牌桌`, "info");
        }
        socket.leave(oldCode);
        socket.data.code = null;
        socket.data.playerId = null;
      }

      let player = room.playerByToken(token);
      const isNew = !player;
      if (!player) {
        player = room.addPlayer(name, token);
      }
      if (!player) {
        failJoin(socket, "加入房间失败，请重试。");
        return;
      }

      const wasOffline = attachSocketToPlayer(socket, room, player);
      socket.emit("joined", {
        protocol: PROTOCOL,
        playerId: player.id,
        code,
        isHost: !!player.isHost,
        view: room.buildView(player.id),
      });
      room.bumpPresence();

      if (isNew) {
        socket.to(code).emit("notice", {
          message: `${player.name} 加入了牌桌`,
          type: "success",
        });
        console.log(`[房间] ${code} ${player.name} 加入`);
      } else if (wasOffline) {
        socket.to(code).emit("notice", {
          message: `${player.name} 重新连回了牌桌`,
          type: "success",
        });
        console.log(`[房间] ${code} ${player.name} 重连`);
      }
    } catch (error) {
      failJoin(
        socket,
        error instanceof GameError ? error.message : "加入房间失败，请重试。",
      );
    }
  });

  /* ---------- 牌局操作 ---------- */
  socket.on("action", (payload) => {
    const code = socket.data.code;
    const playerId = socket.data.playerId;
    if (!code || !playerId) {
      socket.emit("action-error", { message: "你还没有加入房间。" });
      return;
    }
    const room = rooms.get(code);
    if (!room) {
      socket.emit("action-error", { message: "房间已经关闭。" });
      return;
    }
    const player = playerById(room.room, playerId);
    if (!player || player.socketId !== socket.id) {
      socket.emit("action-error", { message: "连接已经失效，请重新进入房间。" });
      return;
    }
    if (!payload?.action || typeof payload.action !== "object") {
      socket.emit("action-error", { message: "无效操作" });
      return;
    }
    try {
      room.handleAction(playerId, payload.action);
    } catch (error) {
      socket.emit("action-error", {
        message:
          error instanceof GameError ? error.message : "操作失败，请重试。",
      });
    }
  });

  /* ---------- 主动离开 ---------- */
  socket.on("leave-room", () => {
    const code = socket.data.code;
    const playerId = socket.data.playerId;
    socket.data.code = null;
    socket.data.playerId = null;
    if (!code || !playerId) {
      socket.emit("left");
      return;
    }
    socket.leave(code);
    const room = rooms.get(code);
    const player = playerById(room?.room, playerId);
    if (room && player && player.socketId === socket.id) {
      player.socketId = null;
      if (room.room.phase === "lobby" && !player.isHost) {
        // 大厅里主动离开：直接释放座位
        room.removeLobbyPlayer(player.id);
      } else {
        // 牌局中主动离开：保留座位，牌局暂停，之后可以用房间码回来
        player.connected = false;
        room.markOffline();
      }
      roomNotice(code, `${player.name} 离开了牌桌`, "info");
      console.log(`[房间] ${code} ${player.name} 离开`);
    }
    socket.emit("left");
  });

  /* ---------- 掉线 ---------- */
  socket.on("disconnect", () => {
    const code = socket.data.code;
    const playerId = socket.data.playerId;
    socket.data.code = null;
    socket.data.playerId = null;
    if (!code || !playerId) return;
    const room = rooms.get(code);
    if (!room) return;
    const player = playerById(room.room, playerId);
    // 如果不是当前绑定的连接（例如旧连接被新连接顶掉），忽略
    if (!player || player.socketId !== socket.id) return;
    player.socketId = null;
    if (player.connected) {
      player.connected = false;
      room.markOffline();
      roomNotice(
        code,
        room.room.phase === "lobby"
          ? `${player.name} 离线了，等待重连`
          : `${player.name} 掉线了，牌局已暂停等待重连`,
        "error",
      );
      console.log(`[房间] ${code} ${player.name} 掉线`);
    }
  });
});

/* 定时回收：全员离线超过 30 分钟的房间自动删除，避免内存泄漏 */
setInterval(() => {
  const now = Date.now();
  for (const [code, room] of rooms) {
    const anyOnline = room.room.players.some((p) => p.connected);
    if (!anyOnline && now - room.lastActivity > ROOM_IDLE_MS) {
      room.clearAutoTimers();
      rooms.delete(code);
      console.log(`[房间] ${code} 已回收（全员离线超过 30 分钟）`);
    }
  }
}, 60 * 1000).unref?.();

/* ============================================================
 * 四、启动
 * ============================================================ */
function getLanAddresses() {
  const list = [];
  const nets = os.networkInterfaces();
  Object.values(nets).forEach((items) => {
    (items || []).forEach((item) => {
      if (item.family === "IPv4" && !item.internal) list.push(item.address);
    });
  });
  return list;
}

httpServer.listen(PORT, HOST, () => {
  console.log("");
  console.log("  UNO 派对桌 · Socket.io 服务已启动");
  console.log(`  本机访问：http://localhost:${PORT}`);
  getLanAddresses().forEach((ip) => {
    console.log(`  局域网访问：http://${ip}:${PORT}`);
  });
  console.log(
    "  跨网络游玩：把服务部署到公网服务器/域名（或使用内网穿透），所有玩家访问同一个地址即可。",
  );
  console.log("");
});

process.on("SIGINT", () => {
  console.log("\n正在关闭服务…");
  io.close(() => httpServer.close(() => process.exit(0)));
});
process.on("SIGTERM", () => {
  io.close(() => httpServer.close(() => process.exit(0)));
});
