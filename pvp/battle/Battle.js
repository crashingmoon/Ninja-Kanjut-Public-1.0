'use strict';

const path      = require('path');
const { v4: uuidv4 } = require('uuid');
const config    = require('../config');
const StatsCalc = require('./StatsCalc');
const TrophyCalc = require('./TrophyCalc');
const SkillData = require('../SkillData');
const ItemData  = require('../ItemData');
const { buildCharacterInfoPayload } = require('../characterInfo');
const db             = require('../db');
const BattleDebugger = require('./BattleDebugger');
const EffectEngine   = require('./EffectEngine');
const EffectCatalog  = require('./EffectCatalog');

// Load pet data once for animation lookups
let _petDataCache = null;
function getPetData() {
  if (!_petDataCache) {
    const petJsonPath = path.join(__dirname, '../../../public/game_data/pet.json');
    try {
      _petDataCache = require(petJsonPath);
    } catch (e) {
      console.error('[PVP] Failed to load pet.json from %s: %s', petJsonPath, e.message);
      _petDataCache = [];
    }
  }
  return _petDataCache;
}
/**
 * Select a pet attack for the current turn.
 * Returns { index, attack } from the pet's attacks array in pet.json.
 * Picks randomly from all unlocked, off-cooldown attacks.
 * Falls back to attacks[0] (basic) if all advanced skills are on cooldown.
 */
function selectPetAttack(petTypeId, petLevel, petCooldowns) {
  const petData = getPetData().find(p => p.id === petTypeId);
  if (!petData || !petData.attacks || !petData.attacks.length) {
    return { index: 0, attack: { animation: 'attack_01', dmg: 1, effects: [], cooldown: 0 } };
  }

  const effectiveLevel = petLevel;

  const available = petData.attacks
    .map((attack, index) => ({ index, attack }))
    .filter(({ index, attack }) =>
      attack.level <= effectiveLevel &&
      !(petCooldowns[index] > 0)
    );

  if (!available.length) {
    // All unlocked skills on cooldown — use basic regardless
    return { index: 0, attack: petData.attacks[0] };
  }

  return available[Math.floor(Math.random() * available.length)];
}

const TURN_DURATION_MS = config.turnDuration * 1000;

// Effect category Sets (SKIP_TURN, DOT, HOT, etc.) are now owned by EffectCatalog.js.
// Battle.js delegates all effect queries to EffectEngine which uses EffectCatalog.

/**
 * Represents a live PvP battle between two characters.
 *
 * Participants are stored in `this.host` / `this.enemy` objects:
 *   { socket, character, stats, skills, cooldowns, buffs }
 *
 * Turn flow:
 *   1. ambush() -> emits Battle.action.ambush to active participant
 *   2. Client emits Battle.action.{weapon|skill|dodge|charge|scroll|run|timeout}
 *   3. processAction() handles it, broadcasts result to both + spectators
 *   4. Server waits for Battle.action.finished from acting client
 *   5. Repeat until battle ends
 */
class Battle {
  /**
   * @param {object} opts
   * @param {object} opts.host    - { socket, character }
   * @param {object} opts.enemy   - { socket, character }
   * @param {object} opts.room    - room info { mode, stage, allowScrolls }
   * @param {Function} opts.onEnd - called with (battle) when battle finishes
   */
  constructor({ host, enemy, room, onEnd }) {
    this.id = uuidv4();
    this.mode  = room.mode  || 'ranked';
    this.stage = room.stage || 'mission_1011';
    this.allowScrolls = !!room.allowScrolls;
    this.onEnd = onEnd;

    this.spectators = new Set();   // socket ids
    this._spectatorSockets = new Map(); // socketId -> socket

    this.round   = 0;
    this.running = false;
    this._turnTimer = null;
    this._awaitingFinished = false;  // waiting for Battle.action.finished
    this._animationOwner   = null;   // participant whose animation we're waiting for
    this._turnOwner        = null;   // participant who received ambush and may act this turn
    this._animationTimer   = null;   // watchdog: fires if finished never arrives
    this._pendingFollowUps = [];     // queued follow-up callbacks (titan mode / eye of mirror / death prevention)
    this._actionLog = [];            // replay log

    // ── Advanced debugger ──────────────────────────────────────────────────
    this._debugger = new BattleDebugger(this.id);

    // ── Effect Engine (PvE-authoritative effect system) ───────────────────
    this._effects = new EffectEngine({
      battle: this,
      debugger: this._debugger,
    });

    this.host  = this._buildParticipant(host.socket,  host.character);
    this.enemy = this._buildParticipant(enemy.socket, enemy.character);

    // Register character names for readable debug output
    this._debugger.registerCharacter(this.host.character.id, this.host.character.name);
    this._debugger.registerCharacter(this.enemy.character.id, this.enemy.character.name);

    // ATB gauge positions (0–600); advanced each turn to determine next actor
    this.host.barX  = 0;
    this.enemy.barX = 0;
    if (this.host.pet)  this.host.pet.barX  = 0;
    if (this.enemy.pet) this.enemy.pet.barX = 0;

    this._petActionPending = null;

    // Determine who goes first via ATB simulation (mirrors client PvPAgilityBarManager)
    const initialWinner = this._advanceATBToNext();
    this._activeParticipant = initialWinner.isPet ? initialWinner.owner : initialWinner;
    if (initialWinner.isPet) this._petActionPending = initialWinner.owner;

    this._bindSocketListeners(this.host);
    this._bindSocketListeners(this.enemy);
  }

  // ─────────────────────────────────────────────────────
  //  Setup helpers
  // ─────────────────────────────────────────────────────

  _buildParticipant(socket, character) {
    const stats   = StatsCalc.buildStats(character);

    // Build base-id → leveled-id map for talent and senjutsu skills so that
    // effect/damage lookups can use the correct leveled entry (e.g. skill_1041:3).
    const talentMap   = this._buildSkillLevelMap(character.talent_skills);
    const senjutsuMap = this._buildSkillLevelMap(character.senjutsu_skills);
    const skillLevelMap = { ...talentMap, ...senjutsuMap };

    const skills  = [
      ...this._parseSkills(character.equipment_skills),
      ...Object.keys(talentMap),
      ...Object.keys(senjutsuMap),
      ...(character.class ? [character.class] : []),
    ];
    const scrolls = [];

    // ── Equipment + Talent + Senjutsu passive effects (delegated to EffectEngine) ─────
    const { buffs: passiveBuffs, unyieldingTalent, maxHpBonus, maxHpPctBonus, talentAgilityPctBonus, talentPassive, senjutsuMaxHpPct, senjutsuPassive, talentAccuracyBonus, talentDodgeBonus, talentCritBonus, talentMaxCpPct } =
      this._effects.bootstrapParticipant(null, character, skillLevelMap);

    // Apply flat talent maxHp bonus (e.g. Saint Physique +100–800)
    if (maxHpBonus > 0) {
      stats.maxHp = Math.max(1, stats.maxHp + maxHpBonus);
    }
    // Apply percent talent maxHp bonus (e.g. Eight Extremities Strengthen +10%)
    if (maxHpPctBonus > 0) {
      stats.maxHp = Math.max(1, Math.round(stats.maxHp * (1 + maxHpPctBonus / 100)));
    }
    // Apply percent talent agility bonus (e.g. Eight Extremities Strengthen +20%)
    if (talentAgilityPctBonus > 0) {
      stats.agility = Math.max(1, Math.round(stats.agility * (1 + talentAgilityPctBonus / 100)));
    }
    // Apply senjutsu max HP bonus (percent, e.g. Mountains Flavor +5–12%)
    if (senjutsuMaxHpPct > 0) {
      stats.maxHp = Math.max(1, Math.round(stats.maxHp * (1 + senjutsuMaxHpPct / 100)));
    }
    // Apply talent accuracy bonus — Dark Eye (skill_1006)
    if (talentAccuracyBonus > 0) stats.accuracy += talentAccuracyBonus;
    // Apply talent dodge bonus — Dark Eye (skill_1006)
    if (talentDodgeBonus > 0) stats.dodgePct += talentDodgeBonus;
    // Apply talent crit chance bonus — Meridian Search (skill_1009)
    if (talentCritBonus > 0) stats.critPct += talentCritBonus;
    // Apply percent maxCp bonus — Meridian Strengthen (skill_1010)
    if (talentMaxCpPct > 0) {
      stats.maxCp = Math.max(1, Math.round(stats.maxCp * (1 + talentMaxCpPct / 100)));
    }
    // Primal Evolution (skill_1052): increase maxHp by % of maxCp — MUST come after maxCp modifications
    const insectMaxHpFromCpPct = talentPassive?.insectMaxHpFromCpPct || 0;
    if (insectMaxHpFromCpPct > 0) {
      stats.maxHp += Math.round(stats.maxCp * insectMaxHpFromCpPct / 100);
    }
    // Knowledge of the Age (skill_1119): increase agility by flat amount per maxHp threshold — MUST come after maxHp modifications
    const agilityFromHpThreshold = talentPassive?.agilityFromHpThreshold || 0;
    const agilityFromHpAmount    = talentPassive?.agilityFromHpAmount    || 0;
    if (agilityFromHpThreshold > 0 && agilityFromHpAmount > 0) {
      stats.agility += Math.floor(stats.maxHp / agilityFromHpThreshold) * agilityFromHpAmount;
    }
    stats.hp = stats.maxHp;
    stats.cp = stats.maxCp; // keep in sync after all maxHp/maxCp modifications

    let pet = null;
    if (character.pet_type_id) {
      const petLvl   = parseInt(character.pet_level, 10) || 1;
      const petMaxHp = 60 + petLvl * 40;
      const petMaxCp = 60 + petLvl * 40;
      const petTypeId = character.pet_swf || character.pet_type_id || '';
      pet = { hp: petMaxHp, maxHp: petMaxHp, cp: petMaxCp, maxCp: petMaxCp,
              agility: 9 + petLvl, stats: { agility: 9 + petLvl },
              typeId: petTypeId, cooldowns: {},
              barX: 0, isPet: true };
    }

    const participant = {
      socket,
      character,
      stats,
      skills,          // array of base skill_id strings (validated against client requests)
      skillLevelMap,   // baseId -> leveledId for talent/senjutsu SkillData lookups
      cooldowns: {},   // skillId -> turns remaining
      buffs: [...passiveBuffs],
      scrolls,
      isDodging: false,
      isCharged: false,
      pet,             // { hp, maxHp, cp, maxCp, agility } or null
      _unyieldingUsed: false,       // one-time death prevention flag
      _unyieldingTalent: unyieldingTalent, // Unyielding Saint talent data (null if not equipped)
      _mirrorOfFreedomUsed: false,  // one-time death prevention flag (EoM talent)
      _classSkillUsed: false,       // one-time class skill flag (Sensor skill_4001)
      _lastSkillUsed:  null,        // tracks last skill for titan mode follow-up
      _exceptionalOnlySkillId: null,
      senjutsuPassive,              // passive config from senjutsu skills (Mountains Flavor, Toad Spirit, etc.)
      talentPassive,                // passive config from talent skills (Eight Extremities damage boost, etc.)
      _usedSkills: new Set(),       // tracks skills used for the first time (Earth Flavor cooldown decrease)
    };
    if (pet) pet.owner = participant;

    // skill_4003 (Offense Class Jutsu): starts with cooldown = skill_cooldown (8 turns).
    // In PvE this is set manually in ActionsManager when the class skill loads.
    // In PvP we set it here so the server enforces the charging gate from turn 1.
    if (character.class) {
      const classSkillBase = character.class.includes(':') ? character.class.split(':')[0] : character.class;
      const classSkillMeta = SkillData.getSkill(character.class);
      const initCd = classSkillMeta ? (classSkillMeta.cooldown || 0) : 0;
      if (initCd > 0) {
        participant.cooldowns[classSkillBase] = initCd;
      }
    }

    return participant;
  }

  _parseSkills(equipmentSkills) {
    if (!equipmentSkills) return [];
    return equipmentSkills
      .split(',')
      .map(s => s.trim())
      .filter(Boolean);
  }

  // Parses "skill_id:level,skill_id:level,..." into a map { baseId -> leveledId }.
  // e.g. "skill_1041:3,skill_1046:5" -> { skill_1041: 'skill_1041:3', skill_1046: 'skill_1046:5' }
  _buildSkillLevelMap(field) {
    if (!field) return {};
    const map = {};
    for (const entry of field.split(',')) {
      const s = entry.trim();
      if (!s) continue;
      const colonIdx = s.indexOf(':');
      if (colonIdx === -1) {
        // No level suffix — use as-is (base skill, no leveled lookup needed)
        map[s] = s;
      } else {
        const baseId    = s.slice(0, colonIdx);
        const leveledId = s;
        if (!map[baseId]) map[baseId] = leveledId; // first occurrence wins
      }
    }
    return map;
  }

  // Kept for backward compatibility (used by _parseSkills in old call sites)
  _parseLeveledSkills(field) {
    return Object.keys(this._buildSkillLevelMap(field));
  }

  _bindSocketListeners(participant) {
    const { socket } = participant;
    const battleId = this.id;

    // Hard guard: rejects any action that isn't allowed this turn.
    // Do NOT re-call getSkipTurnInfo() here — _tickBuffs already expired the
    // skip effect (duration=1 case) before _finishNextTurn ran, so a live check
    // always returns skip=false even though the restriction is still in force.
    // Instead, rely solely on _exceptionalOnlySkillId which is set at turn-start
    // and cleared only when the exceptional action is actually executed:
    //   - null  → no restriction (shouldSkip was false, or skip path already returned)
    //   - set   → only that skill ID is allowed; everything else is locked
    const _isSkipLocked = (p, incomingSkillId) => {
      if (!p._exceptionalOnlySkillId) return false;
      return incomingSkillId !== p._exceptionalOnlySkillId;
    };
    const _skipEffectName = (p) => p._skipEffectName || 'Stunned';

    // Helper: send skip-locked rejection to client so they don't silently wait 20s.
    // Does NOT re-emit ambush — the server skip flow handles turn advancement.
    const _rejectSkipLocked = (action, skipEffectName) => {
      participant.socket.emit(`Battle.action.${action}`, {
        id: participant.character.id,
        error: `Cannot act — ${skipEffectName} is active`,
      });
    };

    socket.on('Battle.action.weapon',  (data) => {
      if (!this.running || data.battle_id !== battleId) return;
      if (this._turnOwner !== participant) {
        this._debugger.logActionGate(participant.character.name, 'weapon', false, 'not_turn_owner');
        return;
      }
      if (_isSkipLocked(participant, null)) {
        this._debugger.logActionGate(participant.character.name, 'weapon', false, 'skip_locked', { skipEffect: _skipEffectName(participant) });
        _rejectSkipLocked('weapon', _skipEffectName(participant));
        return;
      }
      this._debugger.logActionGate(participant.character.name, 'weapon', true, 'allowed');
      this._turnOwner = null;
      this._handleWeapon(participant);
    });

    socket.on('Battle.action.skill', (data) => {
      if (!this.running || data.battle_id !== battleId) return;
      if (this._turnOwner !== participant) {
        this._debugger.logActionGate(participant.character.name, 'skill', false, 'not_turn_owner');
        return;
      }
      const incomingSkillId = data.skillId || data.skill_id;
      if (_isSkipLocked(participant, incomingSkillId)) {
        this._debugger.logActionGate(participant.character.name, 'skill', false, 'skip_locked', { skillId: incomingSkillId, skipEffect: _skipEffectName(participant) });
        _rejectSkipLocked('skill', _skipEffectName(participant));
        return;
      }
      this._debugger.logActionGate(participant.character.name, 'skill', true, 'allowed', { skillId: incomingSkillId });
      this._turnOwner = null;
      this._handleSkill(participant, incomingSkillId);
    });

    socket.on('Battle.action.dodge', (data) => {
      if (!this.running || data.battle_id !== battleId) return;
      if (this._turnOwner !== participant) {
        this._debugger.logActionGate(participant.character.name, 'dodge', false, 'not_turn_owner');
        return;
      }
      if (_isSkipLocked(participant, null)) {
        // Special case: player has an exceptional skill (Sensor class skill_4001) but pressed
        // dodge instead. Treat as a timeout — advance via _handleTimeout so the stun turn is
        // properly consumed without the 22-second wait. This does NOT allow bypassing stun.
        if (participant._exceptionalOnlySkillId) {
          this._debugger.logActionGate(participant.character.name, 'dodge', true, 'exceptional_timeout');
          this._turnOwner = null;
          this._handleTimeout(participant);
          return;
        }
        const skipEff = this._effects.getSkipTurnInfo(participant).effectName || 'unknown';
        this._debugger.logActionGate(participant.character.name, 'dodge', false, 'skip_locked', { skipEffect: skipEff });
        _rejectSkipLocked('dodge', skipEff);
        return;
      }
      this._debugger.logActionGate(participant.character.name, 'dodge', true, 'allowed');
      this._turnOwner = null;
      this._handleDodge(participant);
    });

    socket.on('Battle.action.charge', (data) => {
      if (!this.running || data.battle_id !== battleId) return;
      if (this._turnOwner !== participant) {
        this._debugger.logActionGate(participant.character.name, 'charge', false, 'not_turn_owner');
        return;
      }
      if (_isSkipLocked(participant, null)) {
        this._debugger.logActionGate(participant.character.name, 'charge', false, 'skip_locked', { skipEffect: _skipEffectName(participant) });
        _rejectSkipLocked('charge', _skipEffectName(participant));
        return;
      }
      this._debugger.logActionGate(participant.character.name, 'charge', true, 'allowed');
      this._turnOwner = null;
      this._handleCharge(participant);
    });

    socket.on('Battle.action.scroll', (data) => {
      if (!this.running || data.battle_id !== battleId) return;
      if (this._turnOwner !== participant) {
        this._debugger.logActionGate(participant.character.name, 'scroll', false, 'not_turn_owner');
        return;
      }
      if (_isSkipLocked(participant, null)) {
        this._debugger.logActionGate(participant.character.name, 'scroll', false, 'skip_locked', { skipEffect: _skipEffectName(participant) });
        _rejectSkipLocked('scroll', _skipEffectName(participant));
        return;
      }
      this._debugger.logActionGate(participant.character.name, 'scroll', true, 'allowed');
      this._turnOwner = null;
      this._handleScroll(participant, data.scroll_id);
    });

    socket.on('Battle.action.run', (data) => {
      if (!this.running || data.battle_id !== battleId) return;
      if (this._turnOwner !== participant) {
        this._debugger.logActionGate(participant.character.name, 'run', false, 'not_turn_owner');
        return;
      }
      if (_isSkipLocked(participant, null)) {
        this._debugger.logActionGate(participant.character.name, 'run', false, 'skip_locked', { skipEffect: _skipEffectName(participant) });
        _rejectSkipLocked('run', _skipEffectName(participant));
        return;
      }
      this._debugger.logActionGate(participant.character.name, 'run', true, 'allowed');
      this._turnOwner = null;
      this._handleRun(participant);
    });

    socket.on('Battle.action.timeout', (data) => {
      if (!this.running || data.battle_id !== battleId) return;
      if (this._turnOwner !== participant) {
        this._debugger.logActionGate(participant.character.name, 'timeout', false, 'not_turn_owner');
        return;
      }
      if (_isSkipLocked(participant, null)) {
        this._debugger.logActionGate(participant.character.name, 'timeout', false, 'skip_locked', { skipEffect: _skipEffectName(participant) });
        _rejectSkipLocked('timeout', _skipEffectName(participant));
        return;
      }
      this._debugger.logActionGate(participant.character.name, 'timeout', true, 'allowed');
      this._turnOwner = null;
      this._handleTimeout(participant);
    });

    socket.on('Battle.action.finished', (data) => {
      if (!this.running || data.battle_id !== battleId) return;

      console.log(
        `[Battle ${this.id}] action.finished recv` +
        ` | action=${data.action}` +
        ` | awaiting=${this._awaitingFinished}` +
        ` | owner=${this._animationOwner?.character?.name ?? 'none'}` +
        ` | from=${participant.character.name}`
      );

      if (!this._awaitingFinished) return;

      // Only accept from the participant who performed the action.
      // Both clients play animations and both emit finished; ignoring the
      // observer's signal prevents premature turn advancement.
      if (this._animationOwner && this._animationOwner !== participant) {
        console.log(
          `[Battle ${this.id}] action.finished REJECTED` +
          ` | expected=${this._animationOwner.character.name}` +
          ` | got=${participant.character.name}`
        );
        return;
      }

      this._awaitingFinished = false;
      this._animationOwner   = null;
      this._stopAnimationTimer();
      this._debugger.logTimerState('_awaitingFinished', false, {
        from: participant.character.name,
        action: data.action,
        pendingFollowUps: this._pendingFollowUps.length,
      });

      // If a follow-up action is queued (titan mode / eye of mirror / death prevention),
      // execute the next one instead of advancing the turn.
      if (this._pendingFollowUps.length > 0) {
        const fn = this._pendingFollowUps.shift();
        fn();
        return;
      }

      // Advance ATB and start the next turn (or pet action) for all action types.
      this._advanceTurnAfterAnimation();
    });

    socket.on('Battle.getPlayerInfo', (data) => {
      if (data.battle_id !== battleId) return;
      const charId = parseInt(data.char_id, 10);
      const participant = this.host.character.id == charId ? this.host
                        : this.enemy.character.id == charId ? this.enemy
                        : null;
      if (!participant) return;
      socket.emit('Battle.getPlayerInfo', this._buildPlayerInfoPayload(participant.character));
    });

    socket.on('Conversation.battle.sendMessage', (data) => {
      if (data.battle_id !== battleId) return;
      this._broadcastBattleChat(socket, data.message);
    });
  }

  // ───────────────────────────────────────────────────── Helpers
  _getExceptionalSkillId(participant) {
    if (!participant || !participant.character || participant.isPet) return null;

    // Sensor class skill only
    if (participant.character.class !== 'skill_4001') return null;
    if (participant._classSkillUsed) return null;
    if (!participant.skills.includes('skill_4001')) return null;
    if ((participant.cooldowns?.['skill_4001'] || 0) > 0) return null;

    const effectiveSkillId = participant.skillLevelMap?.['skill_4001'] ?? 'skill_4001';
    const cpCost = StatsCalc.skillCpCost(participant, effectiveSkillId);
    const rawSpCost = StatsCalc.skillSpCost(effectiveSkillId);
    const spCost = (rawSpCost > 0 && this._hasActiveEffect(participant, 'sage_mode')) ? 0 : rawSpCost;

    if ((participant.stats.cp || 0) < cpCost) return null;
    if ((participant.stats.sp || 0) < spCost) return null;

    return 'skill_4001';
  }

  _clearExceptionalOnly(participant) {
    if (participant) {
      participant._exceptionalOnlySkillId = null;
      participant._skipEffectName = null;
      participant._turnRestrictionDisplayBuffs = [];
    }
  }

  /**
   * After _tickBuffs() runs at turn start, compare the pre-tick snapshot with
   * the live buff list to find any control effects that expired (duration=1 → 0).
   * Stores a display-only copy on the participant so clients still see the icon
   * during the restricted turn even though the real buff is already gone.
   * The snapshot is cleared on the next _switchTurn() via _clearExceptionalOnly().
   */
  _captureTurnRestrictionDisplay(participant, turnInfo, preTickBuffs) {
    participant._turnRestrictionDisplayBuffs = [];
    if (!preTickBuffs) return;
    if (!turnInfo.skip && !turnInfo.chaos && !turnInfo.tease) return;

    for (const b of preTickBuffs) {
      if (b.duration <= 0) continue;
      const isControl = EffectCatalog.isSkipTurn(b.effect)
        || EffectCatalog.isChaos(b.effect)
        || EffectCatalog.isTease(b.effect);
      if (!isControl) continue;

      // Was this buff removed or expired during _tickBuffs?
      const live = participant.buffs.find(lb => lb.effect === b.effect);
      if (!live || live.duration <= 0) {
        participant._turnRestrictionDisplayBuffs.push({ ...b });
      }
    }
  }


  // ─────────────────────────────────────────────────────
  //  Public interface
  // ─────────────────────────────────────────────────────

  start() {
    this.running = true;
    this.round   = 0;

    const payload = {
      battleId:   this.id,
      background: this.stage,
      hostId:     this.host.character.id,
      enemyId:    this.enemy.character.id,
    };

    this.host.socket.emit('Battle.started',  { ...payload, isHost: true  });
    this.enemy.socket.emit('Battle.started', { ...payload, isHost: false });

    this._broadcastSpectators('Battle.started', payload);

    // Send initial skill info so tooltips and cooldown display work from turn 1
    this._sendUpdateInfo(this.host);
    this._sendUpdateInfo(this.enemy);

    // Slight delay before first turn so clients have time to load
    setTimeout(() => this._nextTurn(), 1000);
  }

  addSpectator(socket) {
    this.spectators.add(socket.id);
    this._spectatorSockets.set(socket.id, socket);
    socket.emit('Battle.spectator.count', this.spectators.size);
    this._broadcastParticipants('Battle.spectator.count', this.spectators.size);
  }

  removeSpectator(socketId) {
    this.spectators.delete(socketId);
    this._spectatorSockets.delete(socketId);
    this._broadcastParticipants('Battle.spectator.count', this.spectators.size);
  }

  handleDisconnect(socket) {
    if (!this.running) return;

    const participant = this._getParticipant(socket.charId);
    if (participant) {
      // Disconnected participant loses
      const winner = participant === this.host ? this.enemy : this.host;
      this._endBattle(winner, 'disconnect');
    } else {
      // Spectator disconnected
      this.removeSpectator(socket.id);
    }
  }

  // ─────────────────────────────────────────────────────
  //  Turn management
  // ─────────────────────────────────────────────────────

  _nextTurn() {
    if (!this.running) return;
    this._stopTurnTimer();
    // Revoke any lingering action permission from the previous turn.
    // Pet turns bypass the socket action handlers so _turnOwner never gets
    // cleared there — without this, a stale _turnOwner lets a player submit
    // actions during their own stun skip.
    this._turnOwner = null;
    this._debugger.logTimerState('_turnOwner', null, { source: '_nextTurn', prev: this._activeParticipant?.character?.name });

    // Zombie-battle guard: if both players are disconnected the battle can never
    // advance naturally. End as a draw so the server doesn't loop indefinitely.
    if (!this.host.socket.connected && !this.enemy.socket.connected) {
      console.warn(`[Battle ${this.id}] Both players disconnected — auto-ending zombie battle`);
      const winner = this.host.stats.hp >= this.enemy.stats.hp ? this.host : this.enemy;
      this._endBattle(winner, 'timeout');
      return;
    }

    this.round++;
    if (this.round > config.maxRounds) {
      // Draw — whoever has more HP wins
      const winner = this.host.stats.hp > this.enemy.stats.hp
        ? this.host
        : this.enemy;
      this._endBattle(winner, 'timeout');
      return;
    }

    // ── Debug: turn start ────────────────────────────────────────────────
    this._debugger.logTurnStart(this.round, this._activeParticipant.character.id, this._activeParticipant.character.name);
    this._debugger.snapshotBoth('turn_start', this.host, this.enemy);
    this._debugger.logBattleState(this.host, this.enemy);
    this._debugger.logTurnDiagnostics(this._activeParticipant, {
      skipInfo: this._effects.getSkipTurnInfo(this._activeParticipant),
      hp: this._activeParticipant.stats.hp, maxHp: this._activeParticipant.stats.maxHp,
      cp: this._activeParticipant.stats.cp, maxCp: this._activeParticipant.stats.maxCp,
      sp: this._activeParticipant.stats.sp,
    });

    // Turn-start SP recovery: 10% of maxSp for the active participant
    this._grantSp(this._activeParticipant, 10);

    // Tick skill cooldowns for the active participant (pet cooldowns tick in _handlePetAutoAttack)
    this._tickCooldowns(this._activeParticipant);
    this._sendUpdateInfo(this._activeParticipant);

    const opponent = this._getOpponent(this._activeParticipant);

    // Apply per-turn buff/debuff effects (DoT, HoT, CoT) for the ACTIVE participant only.
    // Effects tick once per the affected player's own turn — ticking both players every
    // half-turn would halve all durations (a 3-turn stun would last only 1 stunned turn).
    // Track HP before per-turn effects for death prevention debugging
    this._activeParticipant._lastHpBeforeDamage = this._activeParticipant.stats.hp;
    opponent._lastHpBeforeDamage = opponent.stats.hp;

    const hpBefore = this._activeParticipant.stats.hp;
    const cpBefore = this._activeParticipant.stats.cp;
    const oppHpBefore = opponent.stats.hp;
    const oppCpBefore = opponent.stats.cp;
    const turnOverlays = this._applyPerTurnEffects(this._activeParticipant, opponent);

    // Capture skip-effect state BEFORE decrementing durations so that a buff
    // with duration=1 still causes one full forced-skip before being removed.
    const turnInfo      = this._effects.getSkipTurnInfo(this._activeParticipant);
    const shouldSkip    = turnInfo.skip;
    const skipEffectName = shouldSkip ? turnInfo.effectName : null;

    // Snapshot live buffs BEFORE _tickBuffs so we can detect which control
    // effects were consumed by the tick (for turn-scoped display preservation).
    const preTickBuffs = (shouldSkip || turnInfo.chaos || turnInfo.tease)
      ? this._activeParticipant.buffs.map(b => ({ ...b }))
      : null;

    // Tick 'immediately' type buff durations at turn start.
    // This MUST run even on skip turns so that stun/petrify/frozen etc. expire
    // correctly. getSkipTurnInfo() is called above BEFORE this so that a
    // duration=1 effect still causes one full skip before being removed.
    this._tickBuffs(this._activeParticipant);

    // Preserve a turn-scoped display copy of any control effect that was
    // consumed by _tickBuffs above (duration=1 → expired). This lets the
    // client still see the stun/petrify icon during the affected turn even
    // though the real buff has already been removed from participant.buffs.
    this._captureTurnRestrictionDisplay(this._activeParticipant, turnInfo, preTickBuffs);

    // Broadcast per-turn stat changes whenever stats actually changed or overlays exist.
    // Always includes activeBuffs so the display updates when buffs tick/expire (e.g. DOT ticks,
    // buff duration decrements). This also covers the case where buffs were cleared on a skip turn.
    const statsChanged = this._activeParticipant.stats.hp !== hpBefore
                      || this._activeParticipant.stats.cp !== cpBefore
                      || opponent.stats.hp !== oppHpBefore
                      || opponent.stats.cp !== oppCpBefore;
    if (turnOverlays.length || statsChanged) {
      const updatePayload = {
        id: this._activeParticipant.character.id,
        stats: [
          this._buildStatPayload(this._activeParticipant),
          this._buildStatPayload(opponent),
        ],
      };
      if (turnOverlays.length) {
        updatePayload.overlays = turnOverlays;
      }
      this._broadcastAll('Battle.updateInfo', updatePayload);
    }

    // Check for deaths caused by DoT — apply death prevention with animation
    const dpActive = this._checkDeathPrevention(this._activeParticipant, 'dot_per_turn');
    const dpOpponent = this._checkDeathPrevention(opponent, 'dot_per_turn');
    const dotPreventions = [];
    if (dpActive.skillId) dotPreventions.push(dpActive);
    if (dpOpponent.skillId) dotPreventions.push(dpOpponent);
    const deathOvls = [...dpActive.overlays, ...dpOpponent.overlays];

    if (dotPreventions.length > 0) {
      // Queue death prevention animations as follow-ups
      for (const dp of dotPreventions) {
        const prevented = dp.participantId === this._activeParticipant.character.id
          ? this._activeParticipant : opponent;
        this._pendingFollowUps.push(() => {
          this._emitDeathPreventionAction(dp, prevented, this._activeParticipant, opponent);
        });
      }
      // Queue continuation of turn after all prevention animations finish
      this._pendingFollowUps.push(() => {
        this._continueNextTurnAfterDotPrevention(shouldSkip, skipEffectName, turnInfo);
      });
      // Start the first follow-up (emits animation, waits for action.finished)
      const fn = this._pendingFollowUps.shift();
      fn();
      return;
    }

    // No prevention animations — broadcast overlays if any and continue
    if (deathOvls.length) {
      this._broadcastAll('Battle.updateInfo', {
        id: this._activeParticipant.character.id,
        stats: [
          { id: this._activeParticipant.character.id, stat: { hp: this._activeParticipant.stats.hp, cp: this._activeParticipant.stats.cp, sp: this._activeParticipant.stats.sp } },
          { id: opponent.character.id,                stat: { hp: opponent.stats.hp,                cp: opponent.stats.cp,                sp: opponent.stats.sp                } },
        ],
        overlays: deathOvls,
      });
    }
    this._finishNextTurn(shouldSkip, skipEffectName, turnInfo);
  }

  /**
   * Continue _nextTurn after DoT death prevention animations have played.
   * Called from the follow-up queue after all prevention action.finished events arrive.
   */
  _continueNextTurnAfterDotPrevention(shouldSkip, skipEffectName, turnInfo) {
    const opponent = this._getOpponent(this._activeParticipant);
    // Re-check for deaths (in case prevention didn't save both participants)
    if (this._activeParticipant.stats.hp <= 0 || opponent.stats.hp <= 0) {
      const winner = this._activeParticipant.stats.hp > 0
        ? this._activeParticipant
        : opponent;
      this._scheduleEndAfterAnimation(winner);
      return;
    }
    this._finishNextTurn(shouldSkip, skipEffectName, turnInfo);
  }

  /**
   * Final phase of _nextTurn: skip check, agility bar, chaos, ambush, turn timer.
   * Shared by the normal path and the DoT-prevention path.
   */
 _finishNextTurn(shouldSkip, skipEffectName, turnInfo) {
  const opponent = this._getOpponent(this._activeParticipant);

  if (this._activeParticipant.stats.hp <= 0 || opponent.stats.hp <= 0) {
    const winner = this._activeParticipant.stats.hp > 0
      ? this._activeParticipant
      : opponent;
    this._scheduleEndAfterAnimation(winner);
    return;
  }

  const isChaos = turnInfo && turnInfo.chaos;
  const isTease = turnInfo && turnInfo.tease;

  // skill_4001 (Sensor exceptional) can bypass full-skip effects (stun, petrify, etc.)
  // but NOT chaos/tease — those force a server-chosen action and must not be bypassed.
  const exceptionalSkillId = (shouldSkip && this._activeParticipant?.character)
    ? this._getExceptionalSkillId(this._activeParticipant)
    : null;

  if (exceptionalSkillId) {
    this._activeParticipant._exceptionalOnlySkillId = exceptionalSkillId;
    this._activeParticipant._skipEffectName = skipEffectName || 'Stunned';
  } else {
    this._clearExceptionalOnly(this._activeParticipant);
    this._activeParticipant._skipEffectName = null;
  }

  // Check if the active participant is stunned/sleeping → forced skip
  if (shouldSkip && !exceptionalSkillId) {
    this._debugger.logTurnSkip(
      this._activeParticipant.character.id,
      this._activeParticipant.character.name,
      skipEffectName
    );

    const skipPayload = {
      id:          this._activeParticipant.character.id,
      action:      'skip',
      effect_name: skipEffectName,
    };

    this._broadcastAll('Battle.action.skip', skipPayload);
    // Send updated buff list after _tickBuffs has expired the skip effect so the
    // client's display reflects the new duration (or removal) immediately.
    this._broadcastAll('Battle.updateInfo', {
      id: this._activeParticipant.character.id,
      stats: [this._buildStatPayload(this._activeParticipant)],
    });
    this._awaitingFinished = false;
    // Reset the skipped player's ATB bar to 0 so they cannot win ATB again
    // immediately after being skipped. Without this, a high-agility player
    // could skip and then instantly win the next ATB tick, acting in the same
    // round. Resetting forces the opponent to act first — matching PvE behavior
    // where a skip always hands the turn to the opponent.
    this._activeParticipant.barX = 0;
    if (this._activeParticipant.pet) this._activeParticipant.pet.barX = 0;
    this._switchTurn();
    // Proceed directly to the next turn (no timer needed since no player input).
    // If the ATB winner was a pet, fire the pet action instead of _nextTurn —
    // otherwise the pet turn is silently skipped and ATB drifts.
    if (this._petActionPending) {
      const petOwner = this._petActionPending;
      this._petActionPending = null;
      setTimeout(() => { if (this.running) this._handlePetAutoAttack(petOwner); }, 1000);
    } else {
      this._nextTurn();
    }
    return;
  }

  // Emit agility bar update so clients render turn-order display
  const attackBarEntries = [
    { i: this.host.character.id,  a: StatsCalc.getLiveAgility(this.host)  },
    { i: this.enemy.character.id, a: StatsCalc.getLiveAgility(this.enemy) },
  ];
  if (this.host.pet)  attackBarEntries.push({ i: String(this.host.character.id)  + '_pet', a: StatsCalc.getLiveAgility(this.host.pet)  });
  if (this.enemy.pet) attackBarEntries.push({ i: String(this.enemy.character.id) + '_pet', a: StatsCalc.getLiveAgility(this.enemy.pet) });
  this._broadcastAll('Battle.startAttackBar', { x: attackBarEntries });

  // chaos / tease: participant cannot choose freely — server forces an action.
  // Must be checked BEFORE broadcasting ambush so the client never shows the action bar
  // for a controlled player unless they are allowed to use the exceptional skill.
  if ((isChaos || isTease) && !exceptionalSkillId) {
    const forcedActor = this._activeParticipant;

    if (isTease) {
      // PvE tease: forced weapon attack
      setImmediate(() => {
        if (!this.running || this._activeParticipant !== forcedActor) return;
        this._handleWeapon(forcedActor);
      });
    } else {
      // chaos: random weapon or charge
      const weaponSealed = this._hasActiveEffect(forcedActor, 'dismantle');
      const forcedAction = (!weaponSealed && Math.random() < 0.5) ? 'weapon' : 'charge';

      setImmediate(() => {
        if (!this.running || this._activeParticipant !== forcedActor) return;
        if (forcedAction === 'weapon') this._handleWeapon(forcedActor);
        else                           this._handleCharge(forcedActor);
      });
    }

    return; // don't send ambush or start the player-input timer
  }

  // Emit ambush to tell clients whose turn it is.
  // _turnOwner is also set inside _startTurnTimer (to handle retry paths like
  // restriction/dismantle that re-emit ambush without going through here).
  // During skip/pet/chaos turns _startTurnTimer is never called, so _turnOwner
  // stays null and action handlers reject any stale client input.
  this._turnOwner = this._activeParticipant;
  this._debugger.logTimerState('_turnOwner', this._activeParticipant.character.name, { source: 'ambush' });
  const ambushPayload = {
    id: this._activeParticipant.character.id,
    exceptionalOnlySkillId: this._activeParticipant._exceptionalOnlySkillId || null,
  };
  this._broadcastAll('Battle.action.ambush', ambushPayload);

  this._startTurnTimer(this._activeParticipant);
  }

  _startTurnTimer(participant) {
    // Grant action permission: any code path that (re-)starts the turn timer also
    // restores _turnOwner so the player can submit their action (including retry
    // paths that re-emit ambush due to restriction / dismantle / etc.).
    this._turnOwner = participant;
    this._debugger.logTimerState('_turnOwner', participant.character.name, { source: '_startTurnTimer' });
    this._turnTimer = setTimeout(() => {
      if (!this.running) return;
      if (this._activeParticipant === participant) {
        this._handleTimeout(participant);
      }
    }, TURN_DURATION_MS + 2000);   // +2s grace for network latency
  }

  _stopTurnTimer() {
    if (this._turnTimer) {
      clearTimeout(this._turnTimer);
      this._turnTimer = null;
    }
  }

  /**
   * Start a watchdog timer for the animation phase.
   * If Battle.action.finished never arrives (e.g. client crash / stall),
   * this fires and forces _nextTurn() so the game is never permanently stuck.
   * Timeout = full turn duration + generous 10 s buffer for slow animations.
   */
  _startAnimationTimer() {
    this._stopAnimationTimer();
    this._animationTimer = setTimeout(() => {
      if (!this.running || !this._awaitingFinished) return;
      console.warn(
        `[Battle ${this.id}] animation watchdog fired – forcing next turn` +
        ` | was awaiting: ${this._animationOwner?.character?.name ?? 'unknown'}`
      );
      this._awaitingFinished = false;
      this._animationOwner   = null;
      this._advanceTurnAfterAnimation();
    }, TURN_DURATION_MS + 10000);
  }

  _stopAnimationTimer() {
    if (this._animationTimer) {
      clearTimeout(this._animationTimer);
      this._animationTimer = null;
    }
  }

  /**
   * Short auto-advance timer for pet turns (3 seconds).
   * Pet animations are brief; we don't rely on the Flash client sending
   * Battle.action.finished (the _lastAmbushCharId guard can silently drop it),
   * so the server advances automatically after ~3 s.  If the client does send
   * finished before the timer fires, _awaitingFinished is already false and the
   * timer callback is a no-op.
   */
  _startPetAnimationTimer() {
    this._stopAnimationTimer();
    this._animationTimer = setTimeout(() => {
      if (!this.running || !this._awaitingFinished) return;
      console.log(
        `[Battle ${this.id}] pet animation auto-advance (3s)` +
        ` | owner=${this._animationOwner?.character?.name ?? 'unknown'}`
      );
      this._awaitingFinished = false;
      this._animationOwner   = null;
      this._advanceTurnAfterAnimation();
    }, 3000);
  }

  // ─────────────────────────────────────────────────────
  //  Action handlers
  // ─────────────────────────────────────────────────────

  _handleWeapon(attacker) {
    this._stopTurnTimer();

    // dismantle: cannot use weapon attack this turn
    if (this._hasActiveEffect(attacker, 'dismantle')) {
      attacker.socket.emit('Battle.action.weapon', {
        id: attacker.character.id, error: 'Weapon sealed by dismantle',
      });
      attacker.socket.emit('Battle.action.ambush', { id: attacker.character.id });
      this._startTurnTimer(attacker);
      return;
    }

    const defender = this._getOpponent(attacker);

    // Attach active buffs so StatsCalc can apply modifiers
    attacker.stats.activeBuffs = attacker.buffs;
    defender.stats.activeBuffs = defender.buffs;

    let { damage, crit, dodged } = StatsCalc.calcWeaponDamage(attacker, defender);

    const extraOverlays = [];

    // Track HP before damage for death prevention debugging
    attacker._lastHpBeforeDamage = attacker.stats.hp;
    defender._lastHpBeforeDamage = defender.stats.hp;

    // Unyielding: defender is immune to all damage
    if (!dodged && damage > 0 && this._hasActiveEffect(defender, 'unyielding')) {
      damage = 0;
    }

    // Senjutsu: Shedding — SP-conditional chance to ignore all damage
    if (!dodged && damage > 0 && StatsCalc.checkSheddingIgnore(defender)) {
      damage = 0;
      extraOverlays.push({ id: defender.character.id, icon: 'h', txt: 'Shedding', color: 65280 });
    }

    if (!dodged && damage > 0) {
      // Snapshot HP before damage (needed for rewind rollback)
      const defenderHpSnapshot = defender.stats.hp;

      // PvE-style damage mitigation pipeline (block, absorb, reflect, shield, etc.)
      const mitigation = this._effects.checkReduceHealthEffects({ attacker, defender, damage, damageSource: 'weapon' });
      damage = mitigation.finalDamage;
      extraOverlays.push(...mitigation.overlays);

      // Apply remaining damage to HP
      if (damage > 0) {
        defender.stats.hp = Math.max(0, defender.stats.hp - damage);
      }

      // guard_below_hp: activate protection buff when HP drops below threshold
      this._checkGuardBelowHp(defender);

      // Counter / reactive effects (rewind, fire_wall, bloodfeed, mortal, etc.)
      const { overlays: counterOvls, rewound } = this._applyCounterEffects(attacker, defender, damage);
      extraOverlays.push(...counterOvls);
      if (rewound && damage > 0) {
        defender.stats.hp = defenderHpSnapshot;
        damage = 0;
      }

      // Weapon on-hit effects (poison, drain_cp_with_attack, etc.)
      const weaponOnHitOvls = this._applyWeaponOnHitEffects(attacker, defender);
      extraOverlays.push(...weaponOnHitOvls);

      // damage_to_hp: if attacker has active damage_to_hp buff, heal by damage * amount / 100
      if (damage > 0) {
        const dthBuff = this._effects.getActiveEffect(attacker, 'damage_to_hp');
        if (dthBuff && !this._effects._isHealBlocked(attacker)) {
          const dthHeal = Math.floor(damage * (dthBuff.amount || 100) / 100);
          if (dthHeal > 0) {
            attacker.stats.hp = Math.min(attacker.stats.maxHp, attacker.stats.hp + dthHeal);
            extraOverlays.push({ id: attacker.character.id, icon: 'h', txt: `Convert +${dthHeal}`, color: 65280 });
          }
        }
      }

      // Talent passive after-hit triggers: Light Heart, Dark Heart, rebound, recovery, freeze
      if (damage > 0) {
        this._effects.checkAfterHitTalentPassives({ attacker, defender, overlays: extraOverlays, damage });
      }

      // Critical hit equipment effects — mirrors PvE checkBurnAfterCritical/checkStunAfterCritical/etc.
      // AS3: triggered when IS_CRITICAL=true && param2>0 in handleDamageAndEffects()
      if (crit && damage > 0) {
        const critOverlays = this._effects.checkCriticalEffects({ attacker, defender });
        extraOverlays.push(...critOverlays);
      }
    }

    // SP recovery: +5% on action (attacker), +5% on getting hit (defender, if not dodged)
    this._grantSp(attacker, 5);
    if (!dodged) this._grantSp(defender, 5);

    // Build damage number overlay shown when the weapon animation hits
    const dmgOverlays = (!dodged && damage > 0)
      ? [{ id: defender.character.id, icon: 'd', txt: String(damage), color: crit ? 16776960 : 16711680 }]
      : [];

    const payload = {
      id:      attacker.character.id,
      action:  'weapon',
      stat:    { hp: attacker.stats.hp, cp: attacker.stats.cp, sp: attacker.stats.sp },
      targets: [defender.character.id],
      dodged,
      crit,
      overlays: [...dmgOverlays, ...extraOverlays],
      stats: [
        { id: attacker.character.id, stat: { hp: attacker.stats.hp, cp: attacker.stats.cp, sp: attacker.stats.sp } },
        { id: defender.character.id, stat: { hp: defender.stats.hp, cp: defender.stats.cp, sp: defender.stats.sp } },
      ],
    };

    this._logAction('weapon', payload);
    this._debugger.logAction('weapon', payload);
    this._debugger.logWeaponAttack(attacker.character.id, attacker.character.name, defender.character.id, defender.character.name, {
      damage, crit, dodged,
      reflected: extraOverlays.some(o => o.txt && o.txt === String(damage) && o.id === attacker.character.id),
      blocked: extraOverlays.some(o => o.txt === 'Block'),
      rewound: extraOverlays.some(o => o.txt === 'Rewind'),
    });
    this._debugger.logDamage(attacker.character.id, defender.character.id, {
      type: 'weapon', finalDmg: damage, crit, dodged,
      hpBefore: defender.stats.hp + damage, hpAfter: defender.stats.hp,
    });
    this._debugger.snapshotBoth('after_weapon', this.host, this.enemy);
    this._broadcastAll('Battle.action.weapon', payload);
    this._awaitingFinished = true;
    this._animationOwner   = attacker;
    this._startAnimationTimer();

    // Send updated cooldowns/stats/activeBuffs to both players after weapon action
    this._sendUpdateInfo(attacker);
    this._sendUpdateInfo(defender);

    // Check deaths (attacker can die from serene_mind or counter-effects like kekkai)
    const { dead: weaponDead, overlays: weaponDeathOvls, preventions: weaponPreventions } = this._checkDeathsAfterDamage(attacker, defender, dodged, 'weapon_attack');
    for (const dp of weaponPreventions) {
      const prevented = dp.participantId === attacker.character.id ? attacker : defender;
      this._pendingFollowUps.push(() => {
        this._emitDeathPreventionAction(dp, prevented, attacker, defender);
      });
    }
    if (weaponDeathOvls.length && weaponPreventions.length === 0) {
      this._broadcastAll('Battle.updateInfo', {
        id: attacker.character.id,
        stats: [
          { id: attacker.character.id, stat: { hp: attacker.stats.hp, cp: attacker.stats.cp, sp: attacker.stats.sp } },
          { id: defender.character.id, stat: { hp: defender.stats.hp, cp: defender.stats.cp, sp: defender.stats.sp } },
        ],
        overlays: weaponDeathOvls,
      });
    }
    if (weaponDead) return;

    // ── Titan Mode follow-up attack ──────────────────────────────────────
    // Titan mode triggers on weapon attacks too (not just skills).
    if (!dodged && damage > 0 && this._hasActiveEffect(attacker, 'titan_mode')) {
      const titanLeveledId = attacker.skillLevelMap?.['skill_1022'];
      if (titanLeveledId) {
        // Eye of Mirror talent titan follow-up
        const titanAttacker = attacker;
        this._pendingFollowUps.push(() => {
          if (!this.running || titanAttacker.stats.hp <= 0 || defender.stats.hp <= 0) {
            this._advanceTurnAfterAnimation();
            return;
          }
          this._handleTitanFollowUp(titanAttacker, defender);
        });
        return; // don't advance turn yet — follow-up queue will handle it
      } else {
        // skill_815 Susanoo follow-up (no Eye of Mirror talent)
        const susanooAttacker = attacker;
        this._pendingFollowUps.push(() => {
          if (!this.running || susanooAttacker.stats.hp <= 0 || defender.stats.hp <= 0) {
            this._advanceTurnAfterAnimation();
            return;
          }
          this._handleSusanooFollowUp(susanooAttacker, defender);
        });
        return; // don't advance turn yet — follow-up queue will handle it
      }
    }
  }

  _handleSkill(attacker, skillId) {
    this._stopTurnTimer();

    // ── Class skill (Sensor skill_4001): one-time use, bypasses all blocks ──
    // PvE: can_use_class_skill = false after first use; bypasses chaos/stun/restriction
    const isClassSkill = skillId === attacker.character.class;
    if (isClassSkill) {
      if (attacker._classSkillUsed) {
        attacker.socket.emit('Battle.action.skill', {
          id: attacker.character.id, error: 'Class skill already used this battle',
        });
        attacker.socket.emit('Battle.action.ambush', { id: attacker.character.id });
        this._startTurnTimer(attacker);
        return;
      }
      // Mark as used — PvE: can_use_class_skill = false
      attacker._classSkillUsed = true;
      attacker._classSkillId   = skillId;  // store exact skillId key for cooldown override
      // Class skills bypass restriction, meridian_seal, unyielding — skip blocking checks
    } else {
      // restriction / meridian_seal: cannot use Ninjutsu this turn
      if (this._hasActiveEffect(attacker, 'restriction')) {
        attacker.socket.emit('Battle.action.skill', {
          id: attacker.character.id, error: 'Skills sealed by restriction',
        });
        attacker.socket.emit('Battle.action.ambush', { id: attacker.character.id });
        this._startTurnTimer(attacker);
        return;
      }
      if (this._hasActiveEffect(attacker, 'meridian_seal')) {
        attacker.socket.emit('Battle.action.skill', {
          id: attacker.character.id, error: 'Skills sealed by meridian seal',
        });
        attacker.socket.emit('Battle.action.ambush', { id: attacker.character.id });
        this._startTurnTimer(attacker);
        return;
      }
      // Unyielding: cannot use any skill — only weapon attacks allowed
      if (this._hasActiveEffect(attacker, 'unyielding')) {
        attacker.socket.emit('Battle.action.skill', {
          id: attacker.character.id, error: 'Skills sealed by Unyielding',
        });
        attacker.socket.emit('Battle.action.ambush', { id: attacker.character.id });
        this._startTurnTimer(attacker);
        return;
      }

      // skill_1005 (Ultimate Dance) requires active extreme_mode buff
      const baseSkillId = skillId.includes(':') ? skillId.split(':')[0] : skillId;
      if (baseSkillId === 'skill_1005' && !this._hasActiveEffect(attacker, 'extreme_mode')) {
        attacker.socket.emit('Battle.action.skill', {
          id: attacker.character.id, error: 'Requires Extreme Mode',
        });
        attacker.socket.emit('Battle.action.ambush', { id: attacker.character.id });
        this._startTurnTimer(attacker);
        return;
      }
    }

    // ── Sage Mode activation (skill_3000) ─────────────────────────────
    // skill_3000 is a special button action, not a regular equipped skill.
    // Mirrors PVE HealthManager.useSageMode(): drains all SP, adds sage_mode buff.
    if (skillId === 'skill_3000') {
      if (attacker.stats.maxSp <= 0 || attacker.stats.sp < attacker.stats.maxSp) {
        attacker.socket.emit('Battle.action.skill', {
          id: attacker.character.id, error: 'Not enough sage points',
        });
        attacker.socket.emit('Battle.action.ambush', { id: attacker.character.id });
        this._startTurnTimer(attacker);
        return;
      }
      if (this._hasActiveEffect(attacker, 'sage_mode')) {
        attacker.socket.emit('Battle.action.skill', {
          id: attacker.character.id, error: 'Sage Mode already active',
        });
        attacker.socket.emit('Battle.action.ambush', { id: attacker.character.id });
        this._startTurnTimer(attacker);
        return;
      }

      // Drain all SP
      attacker.stats.sp = 0;

      // Add sage_mode buff (duration 5 turns, +5% damage — mirrors PVE)
      attacker.buffs.push({
        effect: 'sage_mode',
        effect_name: 'Sage Mode',
        type: 'Buff',
        duration: 5,
        amount: 5,
        calc_type: 'percent',
        duration_deduct: 'after_attack',
        is_passive: false,
      });

      const defender = this._getOpponent(attacker);
      const payload = {
        id:       attacker.character.id,
        skillId:  'skill_3000',
        skillName: 'Sage Mode',
        action:   'skill',
        stat:     { hp: attacker.stats.hp, cp: attacker.stats.cp, sp: attacker.stats.sp },
        targets:  [defender.character.id],
        dodged:   false,
        crit:     false,
        overlays: [{ id: attacker.character.id, icon: 'h', txt: 'Sage Mode', color: 65280 }],
        stats: [
          { id: attacker.character.id, stat: { hp: attacker.stats.hp, cp: attacker.stats.cp, sp: attacker.stats.sp } },
          { id: defender.character.id, stat: { hp: defender.stats.hp, cp: defender.stats.cp, sp: defender.stats.sp } },
        ],
      };

      this._logAction('skill', payload);
      this._debugger.logAction('sage_mode_activate', { id: attacker.character.id });
      this._broadcastAll('Battle.action.skill', payload);
      this._awaitingFinished = true;
      this._animationOwner   = attacker;
      this._startAnimationTimer();
      this._sendUpdateInfo(attacker);
      return;
    }

    // Validate skill is equipped and not on cooldown
    if (!skillId || !attacker.skills.includes(skillId)) {
      attacker.socket.emit('Battle.action.skill', {
        id: attacker.character.id, error: 'Skill not available',
      });
      attacker.socket.emit('Battle.action.ambush', { id: attacker.character.id });
      this._startTurnTimer(attacker);
      return;
    }

    if ((attacker.cooldowns[skillId] || 0) > 0) {
      attacker.socket.emit('Battle.action.skill', {
        id: attacker.character.id, error: 'Skill is on cooldown',
      });
      attacker.socket.emit('Battle.action.ambush', { id: attacker.character.id });
      this._startTurnTimer(attacker);
      return;
    }

    // Resolve the leveled skill ID (e.g. "skill_1041:3") for SkillData lookups.
    // Validation and cooldown tracking always use the base skillId the client sent.
    const effectiveSkillId = attacker.skillLevelMap?.[skillId] ?? skillId;

    // cp_cost debuff: inflates the chakra cost of the skill
    // Class skills always cost 0 CP (PvE: cp_cost=0 in skill data, no deduction)
    let cpCost = isClassSkill ? 0 : StatsCalc.skillCpCost(attacker, effectiveSkillId);
    if (!isClassSkill) {
      for (const b of attacker.buffs) {
        if (b.duration > 0 && b.effect === 'cp_cost' && b.calc_type === 'percent') {
          cpCost = Math.floor(cpCost * (1 + b.amount / 100));
        }
      }
    }
    // Domain expansion / after_reality: all skills become free to cast for the duration
    if (this._hasActiveEffect(attacker, 'domain_expansion') || this._hasActiveEffect(attacker, 'after_reality')) {
      cpCost = 0;
    }

    if (attacker.stats.cp < cpCost) {
      attacker.socket.emit('Battle.action.skill', {
        id: attacker.character.id, error: 'Not enough chakra',
      });
      attacker.socket.emit('Battle.action.ambush', { id: attacker.character.id });
      this._startTurnTimer(attacker);
      return;
    }

    // SP cost validation and deduction
    // Sage Mode bypasses SP cost for senjutsu skills (mirrors client EffectsManager)
    const rawSpCost = StatsCalc.skillSpCost(effectiveSkillId);
    const spCost = (rawSpCost > 0 && this._hasActiveEffect(attacker, 'sage_mode')) ? 0 : rawSpCost;
    if (attacker.stats.sp < spCost) {
      attacker.socket.emit('Battle.action.skill', {
        id: attacker.character.id, error: 'Not enough sage points',
      });
      attacker.socket.emit('Battle.action.ambush', { id: attacker.character.id });
      this._startTurnTimer(attacker);
      return;
    }
    attacker.stats.sp = Math.max(0, attacker.stats.sp - spCost);

    // Deduct CP and set real cooldown from skill data
    attacker.stats.cp = Math.max(0, attacker.stats.cp - cpCost);
    attacker.cooldowns[skillId] = StatsCalc.getSkillCooldown(effectiveSkillId);

    // Senjutsu: Earth Flavor — reduce cooldown by cooldown_decrease on first use of each skill
    const cdDecrease = attacker.senjutsuPassive?.cooldownDecrease || 0;
    if (cdDecrease > 0 && !attacker._usedSkills.has(skillId)) {
      attacker._usedSkills.add(skillId);
      attacker.cooldowns[skillId] = Math.max(0, attacker.cooldowns[skillId] - cdDecrease);
    }

    const defender = this._getOpponent(attacker);

    // Attach active buffs so StatsCalc can apply modifiers
    attacker.stats.activeBuffs = attacker.buffs;
    defender.stats.activeBuffs = defender.buffs;

    let { damage, crit, dodged } = StatsCalc.calcSkillDamage(attacker, defender, effectiveSkillId);

    const extraOverlays = [];

    // ── skill_4000 (Medical Class Jutsu): self-heal, no damage pipeline ──────────
    // PvE formula: floor(70 * level - 3200). At lv60 = 1000 HP, lv80 = 2400 HP.
    const _baseSkillId = skillId.includes(':') ? skillId.split(':')[0] : skillId;
    if (_baseSkillId === 'skill_4000') {
      const _level = attacker.character.level || 60;
      const _healAmt = Math.max(0, Math.floor(70 * _level - 3200));
      if (_healAmt > 0 && !this._effects._isHealBlocked(attacker)) {
        attacker.stats.hp = Math.min(attacker.stats.maxHp, attacker.stats.hp + _healAmt);
      }
      this._grantSp(attacker, 5);
      const _healPayload = {
        id: attacker.character.id, skillId, skillName: 'Medical Class Jutsu',
        action: 'skill', stat: { hp: attacker.stats.hp, cp: attacker.stats.cp, sp: attacker.stats.sp },
        targets: [attacker.character.id], dodged: false, crit: false,
        overlays: [{ id: attacker.character.id, icon: 'h', txt: `HP +${_healAmt}`, color: 65280 }],
        stats: [
          { id: attacker.character.id, stat: { hp: attacker.stats.hp, cp: attacker.stats.cp, sp: attacker.stats.sp } },
          { id: defender.character.id, stat: { hp: defender.stats.hp, cp: defender.stats.cp, sp: defender.stats.sp } },
        ],
      };
      this._logAction('skill', _healPayload);
      this._broadcastAll('Battle.action.skill', _healPayload);
      this._sendUpdateInfo(attacker);
      this._sendUpdateInfo(defender);
      this._nextTurn(attacker);
      return;
    }

    // ── skill_4004 (Assault Class Jutsu): damage = floor((64*(lvl-60)+700)*(curHP/maxHP)) ─
    // PvE: BattleVars.CAN_NOT_DODGE = true (always hits), ignores target status.
    if (_baseSkillId === 'skill_4004') {
      const _atkLevel = attacker.character.level || 60;
      const _defMaxHp = defender.stats.maxHp || 1;
      const _defCurHp = defender.stats.hp;
      damage = Math.max(1, Math.floor((64 * (_atkLevel - 60) + 700) * (_defCurHp / _defMaxHp)));
      dodged = false;
      crit   = false;
    }

    // Track HP before damage for death prevention debugging
    attacker._lastHpBeforeDamage = attacker.stats.hp;
    defender._lastHpBeforeDamage = defender.stats.hp;

    // Unyielding: defender is immune to all damage
    if (!dodged && damage > 0 && this._hasActiveEffect(defender, 'unyielding')) {
      damage = 0;
    }

    // Senjutsu: Shedding — SP-conditional chance to ignore all damage
    if (!dodged && damage > 0 && StatsCalc.checkSheddingIgnore(defender)) {
      damage = 0;
      extraOverlays.push({ id: defender.character.id, icon: 'h', txt: 'Shedding', color: 65280 });
    }

    if (!dodged && damage > 0) {
      // Snapshot HP before damage (needed for rewind rollback)
      const defenderHpSnapshotSkill = defender.stats.hp;

      // PvE-style damage mitigation pipeline (block, absorb, reflect, shield, etc.)
      const mitigation = this._effects.checkReduceHealthEffects({ attacker, defender, damage, damageSource: 'skill' });
      damage = mitigation.finalDamage;
      extraOverlays.push(...mitigation.overlays);

      // Apply remaining damage to HP
      if (damage > 0) {
        defender.stats.hp = Math.max(0, defender.stats.hp - damage);
      }

      // guard_below_hp: activate protection buff when HP drops below threshold
      this._checkGuardBelowHp(defender);

      // Counter / reactive effects (rewind, fire_wall, bloodfeed, mortal, etc.)
      const { overlays: counterOvlsSkill, rewound: rewoundSkill } = this._applyCounterEffects(attacker, defender, damage);
      extraOverlays.push(...counterOvlsSkill);
      if (rewoundSkill && damage > 0) {
        defender.stats.hp = defenderHpSnapshotSkill;
        damage = 0;
      }
    }

    // Talent passive after-hit triggers: Light Heart, Dark Heart, rebound, recovery, freeze
    if (!dodged && damage > 0) {
      this._effects.checkAfterHitTalentPassives({ attacker, defender, overlays: extraOverlays, damage });
    }

    // Critical hit equipment effects — mirrors PvE checkBurnAfterCritical/checkStunAfterCritical/etc.
    if (!dodged && crit && damage > 0) {
      const critOvls = this._effects.checkCriticalEffects({ attacker, defender });
      extraOverlays.push(...critOvls);
    }

    // Weapon on-hit equipment effects on skill hits — mirrors PvE handleDamageAndEffects()
    // AS3 calls checkBurnAfterDidDamage, checkBleedingAfterDidDamage, checkSlowAttacker etc.
    // for ALL damaging hits (weapon AND skill), reading from attacker equipment effects.
    if (!dodged && damage > 0) {
      const skillOnHitOvls = this._applyWeaponOnHitEffects(attacker, defender);
      extraOverlays.push(...skillOnHitOvls);
    }

    // ── Genjutsu Rebound (skill_1019 — Crescent Eye of Mirror passive) ──────────
    // If the attacker used a genjutsu (skill_type===7) and the defender has
    // skill_1019 unlocked, roll the talent's chance%. On success all debuffs
    // are redirected back to the attacker instead of the defender.
    // Mirrors AS3 BattleVars.GENJUTSU_REBOUND / _loc5_ = this.attacker_model logic.
    // Does not trigger if dodged or if the defender has used Mirror of Freedom.
    const _usedSkillMeta = SkillData.getSkill(effectiveSkillId);
    let genjutsuRebound = false;
    if (!dodged && _usedSkillMeta.skill_type === 7 && !defender._mirrorOfFreedomUsed) {
      const _reboundLeveledId = defender.skillLevelMap?.['skill_1019'];
      if (_reboundLeveledId) {
        const _reboundData = SkillData.getTalentPassive(_reboundLeveledId);
        if (_reboundData && _reboundData.chance > 0 && Math.random() * 100 < _reboundData.chance) {
          genjutsuRebound = true;
        }
      }
    }

    // ── Apply skill effects (buffs / debuffs) ──────────────────────────────
    // If genjutsu rebound triggered, pass attacker as the effect target so
    // debuffs land on them rather than the defender.
    const effectTarget = genjutsuRebound ? attacker : defender;
    const effectOverlays = this._applySkillEffects(effectiveSkillId, attacker, effectTarget, dodged);
    if (genjutsuRebound) {
      // Show "Genjutsu Rebound" floating text on the defender (matches AS3 createDisplay call)
      effectOverlays.push({ id: defender.character.id, txt: 'Genjutsu Rebound', color: 0x9900FF });
    }

    // damage_to_hp: if attacker has active damage_to_hp buff, heal by damage * amount / 100
    // Must be checked AFTER applySkillEffects so the buff from the current skill exists
    if (!dodged && damage > 0) {
      const dthBuffSkill = this._effects.getActiveEffect(attacker, 'damage_to_hp');
      if (process.env.PVP_DEBUG_EFFECTS === '1' || process.env.PVP_DEBUG_VERBOSE === '1') {
        console.log(`[DTH DEBUG] dodged=${dodged} damage=${damage} buff=${!!dthBuffSkill} healBlocked=${this._effects._isHealBlocked(attacker)} buffEffect=${dthBuffSkill?.effect} buffDur=${dthBuffSkill?.duration} buffAmt=${dthBuffSkill?.amount}`);
      }
      if (dthBuffSkill && !this._effects._isHealBlocked(attacker)) {
        const dthHealSkill = Math.floor(damage * (dthBuffSkill.amount || 100) / 100);
        if (dthHealSkill > 0) {
          attacker.stats.hp = Math.min(attacker.stats.maxHp, attacker.stats.hp + dthHealSkill);
          extraOverlays.push({ id: attacker.character.id, icon: 'h', txt: `Convert +${dthHealSkill}`, color: 65280 });
        }
      }
    }

    // Damage number overlay shown at the animation hit point
    const dmgOverlays = (!dodged && damage > 0)
      ? [{ id: defender.character.id, icon: 'd', txt: String(damage), color: crit ? 16776960 : 16711680 }]
      : [];

    // SP recovery: +5% on action (attacker), +5% on getting hit (defender, if not dodged)
    this._grantSp(attacker, 5);
    if (!dodged) this._grantSp(defender, 5);

    const skillName = _usedSkillMeta.skill_name || '';

    const payload = {
      id:       attacker.character.id,
      skillId,
      skillName,
      action:   'skill',
      stat:     { hp: attacker.stats.hp, cp: attacker.stats.cp, sp: attacker.stats.sp },
      targets:  [defender.character.id],
      dodged,
      crit,
      // Damage number first, then buff/debuff name labels, then counter-effect labels
      overlays: [
        ...dmgOverlays,
        ...effectOverlays.map(o => ({
          id:    o.recipientId,
          icon:  o.buffType === 'Buff' ? 'h' : 'd',
          txt:   o.effectName,
          color: o.buffType === 'Buff' ? 65280 : 16711680,
        })),
        ...extraOverlays,
      ],
      stats: [
        { id: attacker.character.id, stat: { hp: attacker.stats.hp, cp: attacker.stats.cp, sp: attacker.stats.sp } },
        { id: defender.character.id, stat: { hp: defender.stats.hp, cp: defender.stats.cp, sp: defender.stats.sp } },
      ],
    };

    this._logAction('skill', payload);
    this._debugger.logAction('skill', { ...payload, skillId: effectiveSkillId });
    this._debugger.logSkillUsage(attacker.character.id, attacker.character.name, defender.character.id, defender.character.name, {
      skillId: effectiveSkillId, skillName,
      damage, crit, dodged, cpCost, spCost,
      reflected: extraOverlays.some(o => o.txt && o.txt === String(damage) && o.id === attacker.character.id),
      blocked: extraOverlays.some(o => o.txt === 'Block'),
      rewound: extraOverlays.some(o => o.txt === 'Rewind'),
    });
    this._debugger.logDamage(attacker.character.id, defender.character.id, {
      type: 'skill', skillId: effectiveSkillId, finalDmg: damage, crit, dodged,
      hpBefore: defender.stats.hp + damage, hpAfter: defender.stats.hp,
    });
    this._debugger.snapshotBoth('after_skill', this.host, this.enemy);
    this._broadcastAll('Battle.action.skill', payload);
    this._awaitingFinished = true;
    this._animationOwner   = attacker;
    this._startAnimationTimer();

    // Send updated cooldowns/stats/activeBuffs to both players after skill action
    this._sendUpdateInfo(attacker);
    this._sendUpdateInfo(defender);

    // Check deaths (attacker can die from serene_mind or counter-effects)
    const { dead: skillDead, overlays: skillDeathOvls, preventions: skillPreventions } = this._checkDeathsAfterDamage(attacker, defender, dodged, `skill:${effectiveSkillId}`);
    for (const dp of skillPreventions) {
      const prevented = dp.participantId === attacker.character.id ? attacker : defender;
      this._pendingFollowUps.push(() => {
        this._emitDeathPreventionAction(dp, prevented, attacker, defender);
      });
    }
    if (skillDeathOvls.length && skillPreventions.length === 0) {
      this._broadcastAll('Battle.updateInfo', {
        id: attacker.character.id,
        stats: [
          { id: attacker.character.id, stat: { hp: attacker.stats.hp, cp: attacker.stats.cp, sp: attacker.stats.sp } },
          { id: defender.character.id, stat: { hp: defender.stats.hp, cp: defender.stats.cp, sp: defender.stats.sp } },
        ],
        overlays: skillDeathOvls,
      });
    }
    if (skillDead) return;

    // ── Titan Mode follow-up attack ──────────────────────────────────────
    // If the attacker has titan_mode active, automatically trigger an extra
    // follow-up after any skill use (damaging or not).
    if (this._hasActiveEffect(attacker, 'titan_mode') && skillId !== 'skill_1022'
        && skillId !== 'skill_815' && !dodged) {
      const titanLeveledId = attacker.skillLevelMap?.['skill_1022'];
      if (titanLeveledId) {
        // Eye of Mirror talent titan follow-up
        const titanAttacker = attacker;
        this._pendingFollowUps.push(() => {
          if (!this.running || titanAttacker.stats.hp <= 0 || defender.stats.hp <= 0) {
            this._advanceTurnAfterAnimation();
            return;
          }
          this._handleTitanFollowUp(titanAttacker, defender);
        });
        return; // don't advance turn yet — follow-up queue will handle it
      } else {
        // skill_815 Susanoo follow-up (no Eye of Mirror talent)
        const susanooAttacker = attacker;
        this._pendingFollowUps.push(() => {
          if (!this.running || susanooAttacker.stats.hp <= 0 || defender.stats.hp <= 0) {
            this._advanceTurnAfterAnimation();
            return;
          }
          this._handleSusanooFollowUp(susanooAttacker, defender);
        });
        return; // don't advance turn yet — follow-up queue will handle it
      }
    }

    // ── Eye of Mirror (defender's passive) ───────────────────────────────
    // After an enemy uses a skill, the defender's Eye of Mirror may trigger
    // a chance-based copy of that skill back at the attacker.
    // Cannot trigger if: died once (unyielding/mirror_of_freedom used), under unyielding,
    // OR under any lock-class debuff (mirrors AS3 checkCopySkill → isUnderLockDebuffs()).
    // AS3 Effects.lock_effects: sleep, frozen, chill, stun, locked, fear, prison, petrify,
    //   chaos, restriction (and pet_ variants).
    // OR if genjutsu rebound already fired (mirrors AS3: !GENJUTSU_REBOUND gates COPY_SKILL).
    const _EOM_LOCK_EFFECTS = [
      'sleep','pet_sleep','frozen','pet_frozen','chill',
      'stun','locked','pet_stun','fear','pet_fear',
      'prison','pet_prison','petrify','pet_petrify',
      'chaos','pet_chaos','restriction','pet_restriction',
    ];
    const mirrorBlocked = defender._unyieldingUsed || defender._mirrorOfFreedomUsed
      || this._hasActiveEffect(defender, 'unyielding')
      || _EOM_LOCK_EFFECTS.some(fx => this._hasActiveEffect(defender, fx));
    if (!dodged && defender.stats.hp > 0 && !mirrorBlocked && !genjutsuRebound) {
      const mirrorBuff = defender.buffs.find(b => b.duration > 0 && b.effect === 'eye_of_mirror');
      if (mirrorBuff && mirrorBuff.chance > 0) {
        const roll = Math.random() * 100;
        if (roll < mirrorBuff.chance) {
          const cpCost = StatsCalc.skillCpCost(effectiveSkillId);
          // Only copy if defender has enough CP; talent skills are not copied
          const isTalent = effectiveSkillId.startsWith('skill_10');
          if (!isTalent && defender.stats.cp >= cpCost) {
            this._pendingFollowUps.push(() => {
              if (!this.running || defender.stats.hp <= 0 || attacker.stats.hp <= 0) {
                this._advanceTurnAfterAnimation();
                return;
              }
              this._handleEyeOfMirrorCopy(defender, attacker, effectiveSkillId);
            });
            return; // don't advance turn yet — follow-up queue will handle it
          }
        }
      }
    }
  }

  _handleDodge(participant) {
    this._stopTurnTimer();

    participant.isDodging = true;

    // SP recovery: +5% on action
    this._grantSp(participant, 5);

    const payload = {
      id:     participant.character.id,
      action: 'dodge',
      overlays: [
        {
          id: participant.character.id,
          txt: 'Skipped Turn',
          color: 16776960
        }
      ]
    };

    this._logAction('dodge', payload);
    this._debugger.logDodge(participant.character.id, participant.character.name);
    this._broadcastAll('Battle.action.dodge', payload);
    this._awaitingFinished = true;
    this._animationOwner   = participant;
    this._startAnimationTimer();
  }

  _handleCharge(participant) {
    this._stopTurnTimer();

    // Respect charge_disable debuff
    if (this._hasActiveEffect(participant, 'charge_disable')) {
      participant.socket.emit('Battle.action.charge', {
        id: participant.character.id, error: 'Charge disabled',
      });
      participant.socket.emit('Battle.action.ambush', { id: participant.character.id });
      this._startTurnTimer(participant);
      return;
    }

    // meridian_seal: cannot charge this turn (weapon only)
    if (this._hasActiveEffect(participant, 'meridian_seal')) {
      participant.socket.emit('Battle.action.charge', {
        id: participant.character.id, error: 'Charge sealed by meridian seal',
      });
      participant.socket.emit('Battle.action.ambush', { id: participant.character.id });
      this._startTurnTimer(participant);
      return;
    }

    const baseGain = StatsCalc.chargeAmount(participant.stats);
    const gain = this._effects.resolveCharge(participant, baseGain);
    participant.stats.cp = Math.min(participant.stats.maxCp, participant.stats.cp + gain);

    // Equipment: increase_cp_charge — extra CP per charge action
    const cpChargeBoost = participant.buffs.find(b => b.duration > 0 && b.effect === 'increase_cp_charge');
    if (cpChargeBoost) {
      const extra = cpChargeBoost.calc_type === 'percent'
        ? Math.floor(participant.stats.maxCp * cpChargeBoost.amount / 100)
        : Math.max(1, Math.floor(cpChargeBoost.amount));
      participant.stats.cp = Math.min(participant.stats.maxCp, participant.stats.cp + extra);
    }

    // Equipment: increase_hp_charge — heal HP on charge action
    const hpChargeBoost = participant.buffs.find(b => b.duration > 0 && b.effect === 'increase_hp_charge');
    if (hpChargeBoost && !this._effects._isHealBlocked(participant)) {
      const hpExtra = hpChargeBoost.calc_type === 'percent'
        ? Math.floor(participant.stats.maxHp * hpChargeBoost.amount / 100)
        : Math.max(1, Math.floor(hpChargeBoost.amount));
      participant.stats.hp = Math.min(participant.stats.maxHp, participant.stats.hp + hpExtra);
    }

    // SP recovery: +5% on action
    this._grantSp(participant, 5);

    const payload = {
      id:     participant.character.id,
      action: 'charge',
      stat:   { hp: participant.stats.hp, cp: participant.stats.cp, sp: participant.stats.sp },
      overlays: [],
    };

    this._logAction('charge', payload);
    this._debugger.logCharge(participant.character.id, participant.character.name, gain);
    this._broadcastAll('Battle.action.charge', payload);
    this._awaitingFinished = true;
    this._animationOwner   = participant;
    this._startAnimationTimer();
  }

  _handleScroll(participant, scrollId) {
    this._stopTurnTimer();

    if (!this.allowScrolls || !scrollId) {
      participant.socket.emit('Battle.action.scroll', {
        id: participant.character.id, error: 'Scrolls not allowed',
      });
      participant.socket.emit('Battle.action.ambush', { id: participant.character.id });
      this._startTurnTimer(participant);
      return;
    }
    // Unyielding: HP cannot be recovered — block scroll usage
    if (this._hasActiveEffect(participant, 'unyielding')) {
      participant.socket.emit('Battle.action.scroll', {
        id: participant.character.id, error: 'Cannot use scrolls under Unyielding',
      });
      participant.socket.emit('Battle.action.ambush', { id: participant.character.id });
      this._startTurnTimer(participant);
      return;
    }

    // Simplified: scroll restores 20% HP
    const heal = Math.floor(participant.stats.maxHp * 0.2);
    participant.stats.hp = Math.min(participant.stats.maxHp, participant.stats.hp + heal);

    // SP recovery: +5% on action
    this._grantSp(participant, 5);

    const payload = {
      id:      participant.character.id,
      action:  'scroll',
      overlays: [],
      stats: [
        { id: participant.character.id, stat: { hp: participant.stats.hp, cp: participant.stats.cp, sp: participant.stats.sp } },
      ],
    };

    this._logAction('scroll', payload);
    this._debugger.logScroll(participant.character.id, participant.character.name, scrollId, { hpHealed: heal });
    this._broadcastAll('Battle.action.scroll', payload);
    this._awaitingFinished = true;
    this._animationOwner   = participant;
    this._startAnimationTimer();
  }

  _handleRun(participant) {
    this._stopTurnTimer();

    const payload = {
      id:     participant.character.id,
      action: 'run',
    };

    this._logAction('run', payload);
    this._broadcastAll('Battle.action.run', payload);

    // The runner loses
    const winner = this._getOpponent(participant);
    this._endBattle(winner, 'run');
  }

  _handlePetAutoAttack(attacker) {
    // Mark this as a pet action so _advanceTurnAfterAnimation skips deducting
    // the player's 'after_attack' buffs (they should only deduct on player turns).
    this._lastActionWasPet = true;

    // Tick pet skill cooldowns at the start of the pet's own ATB turn
    for (const idx of Object.keys(attacker.pet.cooldowns)) {
      if (attacker.pet.cooldowns[idx] > 0) attacker.pet.cooldowns[idx]--;
    }

    // NOTE: We intentionally do NOT broadcast Battle.action.ambush here.
    // handleAmbushAction() on the Flash client shows the pet owner's action bar
    // and starts their 20-second turn timer when it receives their own ID —
    // which would make the pet owner think it is their player turn while the
    // pet is actually animating.  The 3-second _startPetAnimationTimer() handles
    // turn advancement without needing Battle.action.finished from the client.
    console.log(
      `[Battle ${this.id}] pet ATB turn` +
      ` | owner=${attacker.character.name}` +
      ` | pet=${attacker.pet.typeId}`
    );

    const defender  = this._getOpponent(attacker);
    const petLevel  = Math.max(1, attacker.pet.agility - 9); // agility = 9 + level
    const { index, attack } = selectPetAttack(attacker.pet.typeId, petLevel, attacker.pet.cooldowns);

    // Set cooldown for the selected skill (basic attack has cooldown 0 — no-op)
    if (attack.cooldown > 0) {
      attacker.pet.cooldowns[index] = attack.cooldown;
    }

    // Determine if this is a self/master-targeted skill (buff on owner, no damage to enemy)
    const isSelfSkill = attack.is_self_skill === true;

    // Base damage * skill multiplier (dmg:0 = pure-effect skill, deals no damage)
    const baseDamage = Math.round(3 * petLevel);
    let damage       = attack.dmg > 0 ? Math.round(baseDamage * attack.dmg) : 0;

    // Unyielding: defender is immune to all damage
    if (damage > 0 && this._hasActiveEffect(defender, 'unyielding')) {
      damage = 0;
    }

    const petExtraOverlays = [];
    if (damage > 0 && !isSelfSkill) {
      // PvE-style damage mitigation pipeline for pet attacks
      const mitigation = this._effects.checkReduceHealthEffects({ attacker, defender, damage, damageSource: 'pet' });
      damage = mitigation.finalDamage;
      petExtraOverlays.push(...mitigation.overlays);

      if (damage > 0) {
        defender.stats.hp = Math.max(0, defender.stats.hp - damage);
      }

      this._checkGuardBelowHp(defender);
    }

    // Apply effects from the skill (burn, stun, guard, disperse, etc.)
    const effectOverlays = this._applyPetAttackEffects(attack, attacker, defender);

    const petId  = String(attacker.character.id) + '_pet';

    // Target the master for self-skills, enemy for offensive skills
    const targetId = isSelfSkill ? attacker.character.id : defender.character.id;

    const payload = {
      id:      petId,
      action:  'pet',
      attack:  attack.animation || 'attack_01',
      targets: [targetId],
      dodged:  false,
      isBuff:  isSelfSkill,
      overlays: [
        ...(damage > 0 ? [{ id: defender.character.id, icon: 'd', txt: String(damage), color: 16711680 }] : []),
        ...effectOverlays,
        ...petExtraOverlays,
      ],
      stats: [
        { id: attacker.character.id, stat: { hp: attacker.stats.hp, cp: attacker.stats.cp, sp: attacker.stats.sp } },
        { id: defender.character.id, stat: { hp: defender.stats.hp, cp: defender.stats.cp, sp: defender.stats.sp } },
      ],
    };

    this._debugger.logPetAttack(attacker.character.id, attacker.character.name, defender.character.id, defender.character.name, {
      damage, attackName: attack.animation, isSelfSkill,
      effects: effectOverlays.map(o => o.txt || o.effect || 'unknown'),
    });
    this._broadcastAll('Battle.action.pet', payload);
    this._awaitingFinished = true;
    this._animationOwner   = attacker;
    console.log(
      `[Battle ${this.id}] pet attack sent` +
      ` | owner=${attacker.character.name}` +
      ` | awaiting finished (3s auto-advance)`
    );
    this._startPetAnimationTimer();

    const dp = this._checkDeathPrevention(defender, 'pet_attack');
    if (dp.skillId) {
      // Queue death prevention animation (mirror_of_freedom / Unyielding Saint)
      this._pendingFollowUps.push(() => {
        this._emitDeathPreventionAction(dp, defender, attacker, defender);
      });
    }
    if (dp.overlays.length) {
      this._broadcastAll('Battle.updateInfo', {
        stats: [
          { id: attacker.character.id, stat: { hp: attacker.stats.hp, cp: attacker.stats.cp, sp: attacker.stats.sp } },
          { id: defender.character.id, stat: { hp: defender.stats.hp, cp: defender.stats.cp, sp: defender.stats.sp } },
        ],
        overlays: dp.overlays,
      });
    }
    if (defender.stats.hp <= 0) {
      this._scheduleEndAfterAnimation(attacker);
    }
  }

  _handleTimeout(participant) {
    this._stopTurnTimer();

    // Forced skip — player did not act in time
    const payload = {
      id:          participant.character.id,
      action:      'skip',
      effect_name: 'Turn skipped (timeout)',
    };

    this._broadcastAll('Battle.action.skip', payload);
    this._broadcastAll('Battle.updateInfo', {
      id: participant.character.id,
      stats: [this._buildStatPayload(participant)],
    });
    this._awaitingFinished = false;
    participant.barX = 0;
    if (participant.pet) participant.pet.barX = 0;
    this._switchTurn();
    // Advance to the next turn so the game never stalls after a timeout.
    // If the ATB winner was a pet, fire the pet action instead — same fix as the stun skip path.
    if (this._petActionPending) {
      const petOwner = this._petActionPending;
      this._petActionPending = null;
      setTimeout(() => { if (this.running) this._handlePetAutoAttack(petOwner); }, 1000);
    } else {
      setImmediate(() => this._nextTurn());
    }
  }

  // ─────────────────────────────────────────────────────
  //  Buff / debuff application
  // ─────────────────────────────────────────────────────

  /**
   * Apply all non-passive effects from a skill's skill-effect list.
   * Returns an overlays array of objects { recipientId, buffType, effectName }
   * so the caller can build the correct client payload.
   *
   * @param {string}  skillId
   * @param {object}  attacker  - participant who used the skill
   * @param {object}  defender  - opponent
   * @param {boolean} dodged    - whether the attack was dodged
   * @returns {Array<{recipientId, buffType, effectName}>}
   */
  _applySkillEffects(skillId, attacker, defender, dodged) {
    return this._effects.applySkillEffects({ skillId, attacker, defender, dodged, sourceKind: 'skill' });
  }

  /**
   * Apply effects from a pet attack's `effects` array.
   * Pet effects use target:"master" (→ attacker) or target:"enemy" (→ defender).
   * Returns an overlays array for the broadcast payload.
   */
  _applyPetAttackEffects(attack, attacker, defender) {
    return this._effects.applyPetEffects({ attack, owner: attacker, defender, sourceKind: 'pet' });
  }

  /**
   * Handle instant (duration=0) effects from pet attacks.
   * Delegated to EffectEngine.applyInstantEffect().
   */
  _applyPetInstantEffect(eff, attacker, defender, recipient) {
    return this._effects.applyInstantEffect({ effect: eff, attacker, defender, recipient, sourceKind: 'pet', sourceId: 'pet' });
  }

  /**
   * Handle instant (duration=0) skill effects.
   * Delegated to EffectEngine.applyInstantEffect().
   */
  _applyInstantEffect(eff, attacker, defender, recipient) {
    return this._effects.applyInstantEffect({ effect: eff, attacker, defender, recipient, sourceKind: 'skill', sourceId: '' });
  }

  // ─────────────────────────────────────────────────────
  //  Per-turn buff processing
  // ─────────────────────────────────────────────────────

  /**
   * Apply per-turn effects (DoT, HoT, CoT, theft drain) for a participant.
   * Delegated to EffectEngine.applyPerTurnEffects().
   */
  _applyPerTurnEffects(participant, opponent) {
    return this._effects.applyPerTurnEffects({ participant, opponent });
  }

  // ─────────────────────────────────────────────────────
  //  Buff/cooldown helpers
  // ─────────────────────────────────────────────────────

  _tickCooldowns(participant) {
    for (const skillId of Object.keys(participant.cooldowns)) {
      if (participant.cooldowns[skillId] > 0) {
        participant.cooldowns[skillId]--;
      }
    }
  }

  _tickBuffs(participant) {
    // Deduct 'immediately' type durations at turn start.
    this._effects.deductDurationOfEffects({ participant, phase: 'turn_start' });
  }

  _hasSkipEffect(participant) {
    return this._effects.hasSkipEffect(participant);
  }

  _getActiveSkipEffectName(participant) {
    return this._effects.getActiveSkipEffectName(participant);
  }

  _hasActiveEffect(participant, effectName) {
    return this._effects.hasActiveEffect(participant, effectName);
  }

  _checkGuardBelowHp(participant) {
    this._effects.checkGuardBelowHp(participant);
  }

  _checkDeathPrevention(participant, damageSource) {
    return this._effects.checkDeathPrevention(participant, damageSource);
  }

  /**
   * Check death for both participants after a damage event.
   * Applies death prevention (unyielding) before ending the battle.
   * Returns { dead: boolean, overlays: Array } — caller should broadcast overlays if any.
   */
  _checkDeathsAfterDamage(attacker, defender, dodged = false, damageSource) {
    const overlays = [];
    const preventions = [];

    // Check attacker first (can die from serene_mind, counter-effects, etc.)
    const atkResult = this._checkDeathPrevention(attacker, damageSource || 'counter/reflect');
    overlays.push(...atkResult.overlays);
    if (atkResult.skillId) preventions.push(atkResult);
    if (attacker.stats.hp <= 0) {
      this._scheduleEndAfterAnimation(defender);
      return { dead: true, overlays, preventions: [] };
    }

    // Check defender (normal damage kills)
    if (!dodged) {
      const defResult = this._checkDeathPrevention(defender, damageSource || 'damage');
      overlays.push(...defResult.overlays);
      if (defResult.skillId) preventions.push(defResult);
      if (defender.stats.hp <= 0) {
        this._scheduleEndAfterAnimation(attacker);
        return { dead: true, overlays, preventions: [] };
      }
    }

    return { dead: false, overlays, preventions };
  }

  /**
   * Emit a death prevention event as a Battle.action.skill so the client plays
   * the passive talent's animation. The handler is already loaded in
   * _character_talent_skills_mc so normal playSkill() finds it.
   * Called as a follow-up after the damage animation finishes.
   */
  _emitDeathPreventionAction(dp, prevented, participant1, participant2) {
    const skillName = SkillData.getSkill(dp.skillId).skill_name || 'Death Prevention';

    const payload = {
      id:        prevented.character.id,
      skillId:   dp.skillId,
      skillName,
      action:    'skill',
      stat:      { hp: prevented.stats.hp, cp: prevented.stats.cp, sp: prevented.stats.sp },
      targets:   [prevented.character.id],
      dodged:    false,
      crit:      false,
      overlays:  dp.overlays,
      stats: [
        { id: participant1.character.id, stat: { hp: participant1.stats.hp, cp: participant1.stats.cp, sp: participant1.stats.sp } },
        { id: participant2.character.id, stat: { hp: participant2.stats.hp, cp: participant2.stats.cp, sp: participant2.stats.sp } },
      ],
    };

    this._logAction('skill (death prevention)', payload);
    this._broadcastAll('Battle.action.skill', payload);
    this._awaitingFinished = true;
    this._animationOwner   = prevented;
    this._startAnimationTimer();
  }

  /**
   * Apply counter-effects that trigger on the ATTACKER when they land a hit on DEFENDER.
   * Delegated to EffectEngine.checkPassiveEffectsAfterBeingHit().
   */
  _applyCounterEffects(attacker, defender, damage) {
    return this._effects.checkPassiveEffectsAfterBeingHit({ attacker, defender, damage });
  }

  /**
   * Apply attacker weapon on-hit effects (poison, drain_cp, etc.) to the defender.
   * Only called on a successful (non-dodged) weapon hit.
   * Delegated to EffectEngine.applyWeaponOnHitEffects().
   */
  _applyWeaponOnHitEffects(attacker, defender) {
    return this._effects.applyWeaponOnHitEffects({ attacker, defender, dodged: false });
  }

  // ─────────────────────────────────────────────────────
  //  Titan Mode follow-up attack
  // ─────────────────────────────────────────────────────

  /**
   * Execute a Titan Mode follow-up attack: the attacker automatically uses
   * skill_1022 as a bonus attack after their main action.
   * The follow-up cannot be dodged.
   */
  _handleTitanFollowUp(attacker, defender) {
    const titanLeveledId = attacker.skillLevelMap?.['skill_1022'];
    if (!titanLeveledId) return;

    console.log(`[Battle ${this.id}] Titan Mode follow-up for ${attacker.character.name}`);

    attacker.stats.activeBuffs = attacker.buffs;
    defender.stats.activeBuffs = defender.buffs;

    const { damage, crit } = StatsCalc.calcSkillDamage(attacker, defender, titanLeveledId);

    const extraOverlays = [];

    let finalDmg = damage;
    if (finalDmg > 0) {
      const defenderHpSnapshot = defender.stats.hp;

      // PvE-style damage mitigation pipeline
      const mitigation = this._effects.checkReduceHealthEffects({ attacker, defender, damage: finalDmg, damageSource: 'skill' });
      finalDmg = mitigation.finalDamage;
      extraOverlays.push(...mitigation.overlays);

      if (finalDmg > 0) {
        defender.stats.hp = Math.max(0, defender.stats.hp - finalDmg);
      }

      this._checkGuardBelowHp(defender);

      const { overlays: counterOvls, rewound } = this._applyCounterEffects(attacker, defender, finalDmg);
      extraOverlays.push(...counterOvls);
      if (rewound && finalDmg > 0) {
        defender.stats.hp = defenderHpSnapshot;
        finalDmg = 0;
      }
    }

    // Apply skill effects from the titan skill.
    // Suppress titan_mode self-reapplication: skill_1022 carries its own titan_mode buff
    // effect which would refresh the active buff's duration back to 5 every follow-up.
    // Flag the attacker so _applySkillEffects skips that one effect.
    attacker._suppressTitanModeReapply = true;
    const effectOverlays = this._applySkillEffects(titanLeveledId, attacker, defender, false);
    attacker._suppressTitanModeReapply = false;

    const dmgOverlays = damage > 0
      ? [{ id: defender.character.id, icon: 'd', txt: String(damage), color: crit ? 16776960 : 16711680 }]
      : [];

    const skillName = SkillData.getSkill(titanLeveledId).skill_name || 'Titan Attack';

    const payload = {
      id:       attacker.character.id,
      skillId:  'skill_1022',
      skillName,
      action:   'skill',
      stat:     { hp: attacker.stats.hp, cp: attacker.stats.cp, sp: attacker.stats.sp },
      targets:  [defender.character.id],
      dodged:   false,
      crit,
      isTitanFollowUp: true,
      overlays: [
        ...dmgOverlays,
        ...effectOverlays.map(o => ({
          id: o.recipientId, icon: o.buffType === 'Buff' ? 'h' : 'd',
          txt: o.effectName, color: o.buffType === 'Buff' ? 65280 : 16711680,
        })),
        ...extraOverlays,
      ],
      stats: [
        { id: attacker.character.id, stat: { hp: attacker.stats.hp, cp: attacker.stats.cp, sp: attacker.stats.sp } },
        { id: defender.character.id, stat: { hp: defender.stats.hp, cp: defender.stats.cp, sp: defender.stats.sp } },
      ],
    };

    this._logAction('skill (titan follow-up)', payload);
    this._broadcastAll('Battle.action.skill', payload);
    this._awaitingFinished = true;
    this._animationOwner   = attacker;
    this._startAnimationTimer();

    // Consume one titan_mode charge. duration_deduct is 'never' so the generic
    // after_attack system never touches it — only actual follow-up executions count.
    const titanBuff = attacker.buffs.find(b => b.effect === 'titan_mode' && b.duration > 0);
    if (titanBuff) {
      titanBuff.duration--;
      if (titanBuff.duration <= 0) {
        attacker.buffs = attacker.buffs.filter(b => b !== titanBuff);
        this._debugger.logBuffTick(attacker.character.id, attacker.character.name, ['titan_mode']);
      }
    }

    // Death checks after titan follow-up
    const { dead, overlays: titanDeathOvls, preventions: titanPreventions } = this._checkDeathsAfterDamage(attacker, defender, false, 'titan_followup');
    for (const dp of titanPreventions) {
      const prevented = dp.participantId === attacker.character.id ? attacker : defender;
      this._pendingFollowUps.push(() => {
        this._emitDeathPreventionAction(dp, prevented, attacker, defender);
      });
    }
    if (titanDeathOvls.length && titanPreventions.length === 0) {
      this._broadcastAll('Battle.updateInfo', {
        id: attacker.character.id,
        stats: [
          { id: attacker.character.id, stat: { hp: attacker.stats.hp, cp: attacker.stats.cp, sp: attacker.stats.sp } },
          { id: defender.character.id, stat: { hp: defender.stats.hp, cp: defender.stats.cp, sp: defender.stats.sp } },
        ],
        overlays: titanDeathOvls,
      });
    }
    // If dead, _scheduleEndAfterAnimation was already called inside _checkDeathsAfterDamage.
    // If alive, the turn will advance when the client sends Battle.action.finished.
  }

  // ─────────────────────────────────────────────────────
  //  Susanoo no Mikoto follow-up (skill_815)
  // ─────────────────────────────────────────────────────

  /**
   * Execute a Susanoo no Mikoto follow-up attack triggered by the titan_mode
   * buff from skill_815 (Kinjutsu: Perfect Susanoo no Mikoto).
   * Effect: reduce target HP by 5% of max HP, 30% chance to disperse all
   * positive status from the target.
   * Uses animation frame 83 (same as skill_815's hit animation).
   */
  _handleSusanooFollowUp(attacker, defender) {
    console.log(`[Battle ${this.id}] Susanoo no Mikoto follow-up for ${attacker.character.name}`);

    attacker.stats.activeBuffs = attacker.buffs;
    defender.stats.activeBuffs = defender.buffs;

    const extraOverlays = [];

    // 5% of max HP damage (cannot be dodged — Susanoo always strikes)
    let finalDmg = Math.floor(defender.stats.maxHp * 0.05);

    if (finalDmg > 0) {
      // PvE-style mitigation pipeline
      const mitigation = this._effects.checkReduceHealthEffects({ attacker, defender, damage: finalDmg, damageSource: 'skill' });
      finalDmg = mitigation.finalDamage;
      extraOverlays.push(...mitigation.overlays);

      if (finalDmg > 0) {
        defender.stats.hp = Math.max(0, defender.stats.hp - finalDmg);
      }

      this._checkGuardBelowHp(defender);

      // Counter effects
      const { overlays: counterOvls, rewound } = this._applyCounterEffects(attacker, defender, finalDmg);
      extraOverlays.push(...counterOvls);
      if (rewound && finalDmg > 0) {
        defender.stats.hp = Math.min(defender.stats.maxHp, defender.stats.hp + finalDmg);
        finalDmg = 0;
      }
    }

    // 30% chance to disperse all positive status from target
    const dispersed = Math.random() * 100 < 30;
    if (dispersed) {
      defender.buffs = defender.buffs.filter(b => b.type !== 'Buff' || b.no_disperse);
      extraOverlays.push({ id: defender.character.id, icon: 'd', txt: 'Disperse', color: 16711680 });
    }

    const dmgOverlays = finalDmg > 0
      ? [{ id: defender.character.id, icon: 'd', txt: String(finalDmg), color: 16711680 }]
      : [];

    const payload = {
      id:       attacker.character.id,
      skillId:  'skill_815',
      skillName: 'Susanoo no Mikoto',
      action:   'skill',
      stat:     { hp: attacker.stats.hp, cp: attacker.stats.cp, sp: attacker.stats.sp },
      targets:  [defender.character.id],
      dodged:   false,
      crit:     false,
      isTitanFollowUp: true,
      overlays: [
        ...dmgOverlays,
        ...extraOverlays,
      ],
      stats: [
        { id: attacker.character.id, stat: { hp: attacker.stats.hp, cp: attacker.stats.cp, sp: attacker.stats.sp } },
        { id: defender.character.id, stat: { hp: defender.stats.hp, cp: defender.stats.cp, sp: defender.stats.sp } },
      ],
    };

    this._logAction('skill (susanoo follow-up)', payload);
    this._broadcastAll('Battle.action.skill', payload);
    this._awaitingFinished = true;
    this._animationOwner   = attacker;
    this._startAnimationTimer();

    // Consume one titan_mode charge
    const titanBuff = attacker.buffs.find(b => b.effect === 'titan_mode' && b.duration > 0);
    if (titanBuff) {
      titanBuff.duration--;
      if (titanBuff.duration <= 0) {
        attacker.buffs = attacker.buffs.filter(b => b !== titanBuff);
      }
    }

    // Death checks after Susanoo follow-up
    const { dead, overlays: susDeathOvls, preventions: susPrev } = this._checkDeathsAfterDamage(attacker, defender, false, 'susanoo_followup');
    for (const dp of susPrev) {
      const prevented = dp.participantId === attacker.character.id ? attacker : defender;
      this._pendingFollowUps.push(() => {
        this._emitDeathPreventionAction(dp, prevented, attacker, defender);
      });
    }
    if (susDeathOvls.length && susPrev.length === 0) {
      this._broadcastAll('Battle.updateInfo', {
        id: attacker.character.id,
        stats: [
          { id: attacker.character.id, stat: { hp: attacker.stats.hp, cp: attacker.stats.cp, sp: attacker.stats.sp } },
          { id: defender.character.id, stat: { hp: defender.stats.hp, cp: defender.stats.cp, sp: defender.stats.sp } },
        ],
        overlays: susDeathOvls,
      });
    }
    // If dead, _scheduleEndAfterAnimation handles it.
    // If alive, turn advances when client sends Battle.action.finished.
  }

  // ─────────────────────────────────────────────────────
  //  Eye of Mirror skill copy
  // ─────────────────────────────────────────────────────

  /**
   * Execute an Eye of Mirror skill copy: the defender automatically copies and
   * uses the enemy's skill back at them.
   */
  _handleEyeOfMirrorCopy(copier, target, skillId) {
    console.log(`[Battle ${this.id}] Eye of Mirror triggered for ${copier.character.name} — copying ${skillId}`);

    const cpCost = StatsCalc.skillCpCost(copier, skillId);
    if (copier.stats.cp < cpCost) return; // not enough CP

    copier.stats.cp = Math.max(0, copier.stats.cp - cpCost);

    copier.stats.activeBuffs = copier.buffs;
    target.stats.activeBuffs = target.buffs;

    const { damage, crit, dodged } = StatsCalc.calcSkillDamage(copier, target, skillId);

    const extraOverlays = [];

    let mirrorFinalDmg = damage;
    if (!dodged && mirrorFinalDmg > 0) {
      const targetHpSnapshot = target.stats.hp;

      // PvE-style damage mitigation pipeline
      const mitigation = this._effects.checkReduceHealthEffects({ attacker: copier, defender: target, damage: mirrorFinalDmg, damageSource: 'skill' });
      mirrorFinalDmg = mitigation.finalDamage;
      extraOverlays.push(...mitigation.overlays);

      if (mirrorFinalDmg > 0) {
        target.stats.hp = Math.max(0, target.stats.hp - mirrorFinalDmg);
      }

      this._checkGuardBelowHp(target);

      const { overlays: counterOvls, rewound } = this._applyCounterEffects(copier, target, mirrorFinalDmg);
      extraOverlays.push(...counterOvls);
      if (rewound && mirrorFinalDmg > 0) {
        target.stats.hp = targetHpSnapshot;
      }
    }

    const effectOverlays = this._applySkillEffects(skillId, copier, target, dodged);

    const dmgOverlays = (!dodged && damage > 0)
      ? [{ id: target.character.id, icon: 'd', txt: String(damage), color: crit ? 16776960 : 16711680 }]
      : [];

    const skillName = SkillData.getSkill(skillId).skill_name || 'Copied Skill';

    const payload = {
      id:        copier.character.id,
      skillId,
      skillName: `Eye of Mirror: ${skillName}`,
      action:    'skill',
      stat:      { hp: copier.stats.hp, cp: copier.stats.cp, sp: copier.stats.sp },
      targets:   [target.character.id],
      dodged,
      crit,
      isEyeOfMirror: true,
      copySkill: true,
      overlays: [
        { id: copier.character.id, icon: 'h', txt: 'Eye of Mirror', color: 0xFFD700 },
        ...dmgOverlays,
        ...effectOverlays.map(o => ({
          id: o.recipientId, icon: o.buffType === 'Buff' ? 'h' : 'd',
          txt: o.effectName, color: o.buffType === 'Buff' ? 65280 : 16711680,
        })),
        ...extraOverlays,
      ],
      stats: [
        { id: copier.character.id, stat: { hp: copier.stats.hp, cp: copier.stats.cp, sp: copier.stats.sp } },
        { id: target.character.id, stat: { hp: target.stats.hp, cp: target.stats.cp, sp: target.stats.sp } },
      ],
    };

    this._logAction('skill (eye of mirror)', payload);
    this._broadcastAll('Battle.action.skill', payload);
    this._awaitingFinished = true;
    this._animationOwner   = copier;
    this._startAnimationTimer();

    // Death checks
    const { overlays: mirrorDeathOvls, preventions: mirrorPreventions } = this._checkDeathsAfterDamage(copier, target, dodged, 'eye_of_mirror');
    for (const dp of mirrorPreventions) {
      const prevented = dp.participantId === copier.character.id ? copier : target;
      this._pendingFollowUps.push(() => {
        this._emitDeathPreventionAction(dp, prevented, copier, target);
      });
    }
    if (mirrorDeathOvls.length && mirrorPreventions.length === 0) {
      this._broadcastAll('Battle.updateInfo', {
        id: copier.character.id,
        stats: [
          { id: copier.character.id, stat: { hp: copier.stats.hp, cp: copier.stats.cp, sp: copier.stats.sp } },
          { id: target.character.id, stat: { hp: target.stats.hp, cp: target.stats.cp, sp: target.stats.sp } },
        ],
        overlays: mirrorDeathOvls,
      });
    }
  }

  /**
   * Send a Battle.updateInfo packet to one participant.
   * Always includes ALL equipped skills so the tooltip can show CP cost
   * even before the first skill is used.
   * Cooldowns are formatted as { cd, cost } objects as the client expects.
   */
  /**
   * Build a lightweight array of active buffs for the client to display as pills.
   */
  _getActiveBuffsForClient(participant) {
    return this._effects.getEnabledEffectsForClient(participant);
  }

  /**
   * Build the stat + activeBuffs object for a participant (used in stat arrays).
   */
  _buildStatPayload(participant) {
    return {
      id:   participant.character.id,
      stat: { hp: participant.stats.hp, cp: participant.stats.cp, sp: participant.stats.sp },
      activeBuffs: this._getActiveBuffsForClient(participant),
    };
  }

  /**
   * Build live combat stats for a participant — HP/CP/SP maximums plus
   * accuracy/dodge/crit/purify/reactive/agility computed from current buffs.
   * Included in every Battle.updateInfo so the client can refresh the stat panel live.
   */
  _buildLiveStats(p) {
    const s = p.stats;
    return {
      hp:       s.hp,
      maxHp:    s.maxHp,
      cp:       s.cp,
      maxCp:    s.maxCp,
      sp:       s.sp,
      maxSp:    s.maxSp || 0,
      accuracy: StatsCalc.getLiveAccuracy(p),
      dodge:    StatsCalc.getLiveDodge(p),
      crit:     StatsCalc.getLiveCritical(p),
      purify:   StatsCalc.getLivePurify(p),
      reactive: StatsCalc.getLiveReactiveForce(p),
      agility:  StatsCalc.getLiveAgility(p),
    };
  }

  _sendUpdateInfo(participant) {
    const cooldowns = {};
    for (const skillId of participant.skills) {
      // For talent/senjutsu skills, look up cost using the leveled ID
      const effectiveId = participant.skillLevelMap?.[skillId] ?? skillId;
      cooldowns[skillId] = {
        cd:   participant.cooldowns[skillId] || 0,
        cost: StatsCalc.skillCpCost(effectiveId),
      };
    }
    // Class skill (skill_4001 etc.): send cd:-1 after it's been used once.
    // Use _classSkillId (set at use-time) so the key exactly matches participant.cooldowns.
    // The client checks cd==-1 in updateSkillsCooldownDisplay to permanently gray out btnClassSkill_1.
    if (participant._classSkillUsed && participant._classSkillId) {
      cooldowns[participant._classSkillId] = { cd: -1, cost: 0 };
    }
    // skill_4003 charging phase: send the decrementing cooldown so the client
    // shows the ball counter on btnClassSkill_1 before the skill becomes usable.
    if (!participant._classSkillUsed && participant.character.class) {
      const csBase = participant.character.class.includes(':')
        ? participant.character.class.split(':')[0]
        : participant.character.class;
      const csCd = participant.cooldowns[csBase] || 0;
      if (csCd > 0) {
        cooldowns[csBase] = { cd: csCd, cost: 0 };
      }
    }
    const opponent = this._getOpponent(participant);
    const update = {
      id:             participant.character.id,
      skillCooldowns: cooldowns,
      stat:           { hp: participant.stats.hp, cp: participant.stats.cp, sp: participant.stats.sp, maxHp: participant.stats.maxHp, maxCp: participant.stats.maxCp },
      liveStats:      this._buildLiveStats(participant),
      activeBuffs:    this._getActiveBuffsForClient(participant),
    };
    if (opponent) {
      update.enemyActiveBuffs = {
        id: opponent.character.id,
        activeBuffs: this._getActiveBuffsForClient(opponent),
      };
      update.enemyLiveStats = {
        id: opponent.character.id,
        ...this._buildLiveStats(opponent),
      };
    }
    if (participant.pet) {
      update.pet = {
        hp:    participant.pet.hp,    maxHp: participant.pet.maxHp,
        cp:    participant.pet.cp,    maxCp: participant.pet.maxCp,
        agility: participant.pet.agility,
      };
    }
    participant.socket.emit('Battle.updateInfo', update);
  }

  // ─────────────────────────────────────────────────────
  //  Turn / end helpers
  // ─────────────────────────────────────────────────────

  /**
   * Called once an animation phase ends (via action.finished, the watchdog, or the pet 3s timer).
   * Advances the ATB, then either triggers a pending pet action or starts the next player turn.
   */
  _advanceTurnAfterAnimation() {
    // PvE-style: deduct 'after_attack' durations now that the action is done.
    // Skip this during pet turns — _activeParticipant stays as the last player
    // during pet actions, so deducting here would burn that player's buffs on
    // every pet attack instead of only on their own turns.
    if (this._activeParticipant && !this._lastActionWasPet) {
      this._effects.deductDurationOfEffects({ participant: this._activeParticipant, phase: 'after_attack' });
    }
    this._lastActionWasPet = false;

    this._switchTurn();
    if (this._petActionPending) {
      const petOwner = this._petActionPending;
      this._petActionPending = null;
      setTimeout(() => { if (this.running) this._handlePetAutoAttack(petOwner); }, 1000);
    } else {
      this._nextTurn();
    }
  }

  _switchTurn() {

    this._clearExceptionalOnly(this.host);
    this._clearExceptionalOnly(this.enemy);

    const winner = this._advanceATBToNext();
    const winnerName = winner.isPet ? `pet(owner=${winner.owner.character.name})` : winner.character.name;
    this._debugger.logAtbWinner(winnerName, {
      isPet: !!winner.isPet,
      ownerId: winner.isPet ? winner.owner.character.id : null,
      charId: winner.isPet ? null : winner.character.id,
    });
    if (winner.isPet) {
      // Pet's ATB slot fired — queue the auto-attack and leave _activeParticipant
      // unchanged. The owner's player turn is determined by the NEXT _switchTurn call
      // (triggered after the pet's Battle.action.finished arrives).
      this._petActionPending = winner.owner;
    } else {
      this._petActionPending = null;
      this._activeParticipant = winner;
    }
  }

  /**
   * ATB (Active Time Battle) gauge simulation — mirrors PvPAgilityBarManager.checkAmbush().
   *
   * Each call advances both participants' gauge positions by their per-tick agility value
   * until at least one reaches 600. The one with the highest position acts next; their
   * overflow (position - 600) carries forward. Others keep their current position so they
   * act sooner relative to the winner in subsequent turns.
   *
   * Per-tick agility formula (matches client ACTION_BAR_DIVIDER = 20):
   *   toRepeat = floor(maxAgility / 20)
   *   advance  = toRepeat > 2 ? floor(agility / toRepeat) : agility
   *
   * Tiebreak: host acts first (mirrors client sortAgilityHeads ID-ascending tiebreak
   * since the host always has the lower socket-assigned character ID in practice).
   */
  _advanceATBToNext() {
    const alivePlayers = [this.host, this.enemy].filter(p => p.stats.hp > 0);
    const alivePets    = alivePlayers.filter(p => p.pet && p.pet.hp > 0).map(p => p.pet);
    const alive        = [...alivePlayers, ...alivePets];

    if (alive.length === 0) return this.host;
    if (alive.length === 1) return alive[0];

    const maxAgi   = Math.max(...alive.map(p => StatsCalc.getLiveAgility(p)));
    const toRepeat = Math.max(1, Math.floor(maxAgi / 20));
    let ticks = 0;

    while (true) {
      ticks++;
      for (const p of alive) {
        const liveAgi = StatsCalc.getLiveAgility(p);
        const advance = toRepeat > 2
          ? Math.floor(liveAgi / toRepeat)
          : liveAgi;
        p.barX += advance;
      }

      const maxX = Math.max(...alive.map(p => p.barX));
      if (maxX >= 600) {
        const reached = alive.filter(p => p.barX >= 600);
        reached.sort((a, b) => {
          if (b.barX !== a.barX) return b.barX - a.barX;   // highest gauge first
          if (a.isPet !== b.isPet) return a.isPet ? 1 : -1; // players before pets in ties
          const aOwner = a.isPet ? a.owner : a;
          const bOwner = b.isPet ? b.owner : b;
          return aOwner === this.host ? -1 : 1;             // host wins remaining ties
        });
        const winner = reached[0];
        const barBeforeCarry = winner.barX;
        winner.barX -= 600; // carry overflow into next cycle
        this._debugger.logAtbResolution({
          winnerName: winner.isPet ? `pet(owner=${winner.owner.character.name})` : winner.character.name,
          winnerId: winner.isPet ? `${winner.owner.character.id}_pet` : winner.character.id,
          isPet: !!winner.isPet,
          ticks,
          maxAgility: maxAgi,
          toRepeat,
          entries: alive.map(p => ({
            id: p.isPet ? `${p.owner.character.id}_pet` : p.character.id,
            name: p.isPet ? `pet(owner=${p.owner.character.name})` : p.character.name,
            agility: StatsCalc.getLiveAgility(p),
            barBefore: p === winner ? barBeforeCarry : p.barX,
            barAfter: p.barX,
          })),
        });
        return winner;
      }
    }
  }

  /**
   * Grant `pct`% of maxSp to a participant, capped at maxSp.
   * No-op for characters below level 80 (maxSp === 0).
   */
  _grantSp(participant, pct) {
    if (participant.stats.maxSp <= 0) return;
    const gain = Math.floor(participant.stats.maxSp * pct / 100);
    if (gain > 0) {
      participant.stats.sp = Math.min(participant.stats.maxSp, participant.stats.sp + gain);
    }
  }

  _scheduleEndAfterAnimation(winner) {
    // Give clients ~2 s to finish the death animation before ending
    setTimeout(() => {
      if (this.running) this._endBattle(winner, 'battle');
    }, 2000);
  }

  async _endBattle(winner, reason) {
    if (!this.running) return;
    this.running = false;
    this._stopTurnTimer();
    this._stopAnimationTimer();

    const loser = winner === this.host ? this.enemy : this.host;

    // Debug: record battle end
    this._debugger.logBattleEnd(winner.character.id, loser.character.id, reason, this.round);
    this._debugger.snapshotBoth('battle_end', this.host, this.enemy);

    // ── Load live PvP settings from DB (60-second cached) ──
    const pvpCfg = await db.getGameConfig('pvp_settings', {});
    this._pvpSettings = {
      pvpPointsWin:   pvpCfg.pvp_points_win   != null ? pvpCfg.pvp_points_win   : config.pvpPointsWin,
      pvpPointsLose:  pvpCfg.pvp_points_lose  != null ? pvpCfg.pvp_points_lose  : config.pvpPointsLose,
      pvpPrestigeWin: pvpCfg.pvp_prestige_win != null ? pvpCfg.pvp_prestige_win : config.pvpPrestigeWin,
      trophyKFactor:  pvpCfg.trophy_k_factor  != null ? pvpCfg.trophy_k_factor  : config.trophyKFactor,
      trophyFloor:    pvpCfg.trophy_floor      != null ? pvpCfg.trophy_floor     : config.trophyFloor,
    };

    // ── Trophy calculation ──
    let trophyInfo = null;
    if (this.mode === 'ranked') {
      trophyInfo = TrophyCalc.applyTrophies(
        winner.character.pvp_trophy || 0,
        loser.character.pvp_trophy  || 0,
        this._pvpSettings.trophyKFactor,
        this._pvpSettings.trophyFloor,
      );
    }
    

    const winnerTrophyAfter = trophyInfo ? trophyInfo.winnerAfter : (winner.character.pvp_trophy || 0);
    const loserTrophyAfter  = trophyInfo ? trophyInfo.loserAfter  : (loser.character.pvp_trophy  || 0);

    // ── Persist to DB ──
    try {
      await this._saveBattle(winner, loser, trophyInfo, winnerTrophyAfter, loserTrophyAfter);
    } catch (err) {
      console.error('[Battle] DB save error:', err.message);
    }

    // ── Build result payloads ──
    // The Flash client checks: data.id === myCharId → Victory, else → Defeat.
    // Both payloads must carry the WINNER's id so only the winner's comparison is true.
    const winnerId = winner.character.id;
    const winnerResult = this._buildResultPayload(winner, true,  trophyInfo, winnerTrophyAfter, loserTrophyAfter, winnerId);
    const loserResult  = this._buildResultPayload(loser,  false, trophyInfo, winnerTrophyAfter, loserTrophyAfter, winnerId);

    winner.socket.emit('Battle.ended', winnerResult);
    loser.socket.emit('Battle.ended',  loserResult);
    this._broadcastSpectators('Battle.ended', winnerResult);

    if (this.onEnd) this.onEnd(this);
  }

  _buildResultPayload(participant, won, trophyInfo, winnerTrophyAfter, loserTrophyAfter, winnerId) {
    const isWinner = won;
    const char = participant.character;

    const trophyDelta = trophyInfo
      ? (isWinner ? trophyInfo.winnerDeltaText : trophyInfo.loserDeltaText)
      : '0';

    const trophyAfter = isWinner ? winnerTrophyAfter : loserTrophyAfter;

    return {
      id:      winnerId,   // always the winner's id — client checks data.id === myCharId for Victory
      won,
      trophy:  trophyDelta,
      trophyAfter,
      rewards: {
        gold:   won ? Math.floor(50 + (parseInt(char.level, 10) || 1) * 2) : 0,
        xp:     won ? Math.floor(100 + (parseInt(char.level, 10) || 1) * 5) : 0,
        points: won ? (this._pvpSettings ? this._pvpSettings.pvpPointsWin : config.pvpPointsWin) : (this._pvpSettings ? this._pvpSettings.pvpPointsLose : config.pvpPointsLose),
        etc:    [],
      },
    };
  }

  async _saveBattle(winner, loser, trophyInfo, winnerTrophyAfter, loserTrophyAfter) {
    const hostWon     = winner === this.host;
    const trophyDelta = trophyInfo ? trophyInfo.delta : 0;

    const hostTrophyBefore  = this.host.character.pvp_trophy  || 0;
    const enemyTrophyBefore = this.enemy.character.pvp_trophy || 0;

    const hostTrophyAfter  = hostWon  ? winnerTrophyAfter : loserTrophyAfter;
    const enemyTrophyAfter = !hostWon ? winnerTrophyAfter : loserTrophyAfter;

    const hostSnap  = this._buildSnapshot(this.host);
    const enemySnap = this._buildSnapshot(this.enemy);

    // Insert battle record
    const [result] = await db.getPool().execute(
      `INSERT INTO pvp_battles
         (host_id, enemy_id, mode, host_won, trophy_delta,
          host_trophy_before, host_trophy_after,
          enemy_trophy_before, enemy_trophy_after,
          host_level, enemy_level, host_rank, enemy_rank,
          host_snapshot, enemy_snapshot, battle_data,
          created_at, updated_at)
       VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,NOW(),NOW())`,
      [
        this.host.character.id,
        this.enemy.character.id,
        this.mode,
        hostWon ? 1 : 0,
        trophyDelta,
        hostTrophyBefore,  hostTrophyAfter,
        enemyTrophyBefore, enemyTrophyAfter,
        this.host.character.level  || 1,
        this.enemy.character.level || 1,
        this.host.character.rank   || 1,
        this.enemy.character.rank  || 1,
        JSON.stringify(hostSnap),
        JSON.stringify(enemySnap),
        JSON.stringify({
          rounds: this.round,
          log: this._actionLog.slice(-100),
          debug: this._debugger.enabled ? this._debugger.getReport() : null,
        }),
      ]
    );

    // Update character stats
    const prestigePerWin = this._pvpSettings ? this._pvpSettings.pvpPrestigeWin : config.pvpPrestigeWin;
    const pointsWin  = this._pvpSettings ? this._pvpSettings.pvpPointsWin  : config.pvpPointsWin;
    const pointsLose = this._pvpSettings ? this._pvpSettings.pvpPointsLose : config.pvpPointsLose;

    await db.getPool().execute(
      `UPDATE characters
       SET pvp_played  = pvp_played  + 1,
           pvp_won     = pvp_won     + ?,
           pvp_lost    = pvp_lost    + ?,
           pvp_trophy  = ?,
           pvp_points  = GREATEST(0, pvp_points + ?),
           prestige    = prestige    + ?
       WHERE id = ?`,
      [hostWon ? 1 : 0, hostWon ? 0 : 1, hostTrophyAfter,
       hostWon ? pointsWin : -pointsLose,
       hostWon ? prestigePerWin : 0,
       this.host.character.id]
    );
    await db.getPool().execute(
      `UPDATE characters
       SET pvp_played  = pvp_played  + 1,
           pvp_won     = pvp_won     + ?,
           pvp_lost    = pvp_lost    + ?,
           pvp_trophy  = ?,
           pvp_points  = GREATEST(0, pvp_points + ?),
           prestige    = prestige    + ?
       WHERE id = ?`,
      [!hostWon ? 1 : 0, !hostWon ? 0 : 1, enemyTrophyAfter,
       !hostWon ? pointsWin : -pointsLose,
       !hostWon ? prestigePerWin : 0,
       this.enemy.character.id]
    );

    // ── Battle Pass XP for both players ──
    try {
      await this._grantBattlePassXp(this.host.character.id);
      await this._grantBattlePassXp(this.enemy.character.id);
    } catch (bpErr) {
      console.error('[Battle] Battle Pass XP error:', bpErr.message);
    }

    return result.insertId;
  }

  async _grantBattlePassXp(charId) {
    const pool = db.getPool();

    // Get active battle pass season
    const [bpRows] = await pool.execute(
      `SELECT season, max_level, xp_per_level FROM battle_passes WHERE active = 1 ORDER BY season DESC LIMIT 1`
    );
    if (!bpRows.length) return;
    const bp = bpRows[0];

    // Get or create progress
    let [progressRows] = await pool.execute(
      `SELECT id, level, xp, is_active FROM character_battle_passes WHERE character_id = ? AND season = ?`,
      [charId, bp.season]
    );
    if (!progressRows.length) {
      // Auto-create with free pass active + unlocked
      await pool.execute(
        `INSERT INTO character_battle_passes (character_id, season, level, xp, is_active, is_premium, unlocked, created_at, updated_at)
         VALUES (?, ?, 1, 0, 1, 0, 1, NOW(), NOW())`,
        [charId, bp.season]
      );
      [progressRows] = await pool.execute(
        `SELECT id, level, xp, is_active FROM character_battle_passes WHERE character_id = ? AND season = ?`,
        [charId, bp.season]
      );
    }
    if (!progressRows.length || !progressRows[0].is_active) return;
    const progress = progressRows[0];

    // Read XP config from game_configs
    const xpConfig = await db.getGameConfig('battle_pass_xp', {
      mission: 5000, eudemon: 10000, hunting: 10000, event: 5000, pvp: 10000, coop: 10000
    });
    const xpGain = parseInt(xpConfig.pvp) || 10000;
    if (xpGain <= 0) return;

    const xpPerLevel = parseInt(bp.xp_per_level) || 25000;
    const maxLevel   = parseInt(bp.max_level) || 50;

    let currentXp    = parseInt(progress.xp) + xpGain;
    let currentLevel = parseInt(progress.level);

    while (currentLevel < maxLevel && currentXp >= xpPerLevel) {
      currentXp -= xpPerLevel;
      currentLevel++;
    }
    if (currentLevel >= maxLevel) {
      currentXp = Math.min(currentXp, xpPerLevel);
    }

    await pool.execute(
      `UPDATE character_battle_passes SET xp = ?, level = ?, updated_at = NOW() WHERE id = ?`,
      [currentXp, currentLevel, progress.id]
    );
  }

  _buildSnapshot(participant) {
    const char = participant.character;
    return {
      id:     char.id,
      name:   char.name,
      rank:   char.rank,
      level:  char.level,
      trophy: char.pvp_trophy || 0,
      skills: participant.skills,
      talents: [char.talent_1, char.talent_2, char.talent_3],
      set: {
        clothing: char.equipment_clothing || 'set_01_0',
        weapon:   char.equipment_weapon   || 'wpn_01',
        back_item: char.equipment_back    || 'back_01',
        hairstyle:  this._formatHair(char),
        face:       this._formatFace(char),
        hair_color: char.hair_color  || '0|0',
        skin_color: char.skin_color  || 'null|null',
      },
    };
  }

  _formatHair(char) {
    const suffix = char.gender == 0 ? '_0' : '_1';
    const h = char.hair_style;
    if (!h) return `hair_01${suffix}`;
    if (isNaN(Number(h))) return h;
    return `hair_${String(h).padStart(2, '0')}${suffix}`;
  }

  _formatFace(char) {
    const suffix = char.gender == 0 ? '_0' : '_1';
    return `face_01${suffix}`;
  }

  // ─────────────────────────────────────────────────────
  //  Broadcast helpers
  // ─────────────────────────────────────────────────────

  _broadcastAll(event, data) {
    // Auto-inject activeBuffs into stats array entries so the client can display buff/debuff pills
    if (data && Array.isArray(data.stats)) {
      for (const entry of data.stats) {
        if (entry && entry.id != null && !entry.activeBuffs) {
          const p = this._getParticipant(entry.id);
          if (p) {
            entry.activeBuffs = this._getActiveBuffsForClient(p);
          }
        }
      }
    }
    this.host.socket.emit(event, data);
    this.enemy.socket.emit(event, data);
    this._broadcastSpectators(event, data);
  }

  _broadcastParticipants(event, data) {
    this.host.socket.emit(event, data);
    this.enemy.socket.emit(event, data);
  }

  _broadcastSpectators(event, data) {
    for (const sock of this._spectatorSockets.values()) {
      sock.emit(event, data);
    }
  }

  _broadcastBattleChat(senderSocket, message) {
    if (!message) return;
    const sender = this._getParticipant(senderSocket.charId);
    if (!sender) return;
    const msg = {
      character: { id: sender.character.id, name: sender.character.name },
      message:   String(message).substring(0, 200),
    };
    this._broadcastAll('Conversation.battle.newMessage', msg);
  }

  // ─────────────────────────────────────────────────────
  //  Utility
  // ─────────────────────────────────────────────────────

  _buildPlayerInfoPayload(character) {
    // CharacterManager.fillCharacterData() expects the same flat format as
    // Client.characterInfo: { id, name, level, stat:{...}, set:{...}, point:{...}, ... }
    // It builds character_data / character_sets / character_points itself from those fields.
    return buildCharacterInfoPayload(character).character;
  }

  _getParticipant(charId) {
    if (this.host.character.id  == charId) return this.host;
    if (this.enemy.character.id == charId) return this.enemy;
    return null;
  }

  _getOpponent(participant) {
    return participant === this.host ? this.enemy : this.host;
  }

  _logAction(type, payload) {
    this._actionLog.push({ round: this.round, type, ...payload });
  }

  getSummary() {
    return {
      battleId: this.id,
      mode:     this.mode,
      stage:    this.stage,
      round:    this.round,
      hostId:   this.host.character.id,
      hostName: this.host.character.name,
      enemyId:  this.enemy.character.id,
      enemyName: this.enemy.character.name,
      spectators: this.spectators.size,
      debug: this._debugger.getSummary(),
    };
  }

  /**
   * Get the full debug report for this battle.
   * Used by the /debug HTTP endpoint for live battle inspection.
   */
  getDebugReport() {
    return {
      ...this.getSummary(),
      hostStats: {
        hp: this.host.stats.hp, maxHp: this.host.stats.maxHp,
        cp: this.host.stats.cp, maxCp: this.host.stats.maxCp,
        sp: this.host.stats.sp,
        buffs: this.host.buffs.filter(b => b.duration > 0).map(b => ({
          effect: b.effect, name: b.effect_name, type: b.type,
          duration: b.duration, amount: b.amount,
        })),
      },
      enemyStats: {
        hp: this.enemy.stats.hp, maxHp: this.enemy.stats.maxHp,
        cp: this.enemy.stats.cp, maxCp: this.enemy.stats.maxCp,
        sp: this.enemy.stats.sp,
        buffs: this.enemy.buffs.filter(b => b.duration > 0).map(b => ({
          effect: b.effect, name: b.effect_name, type: b.type,
          duration: b.duration, amount: b.amount,
        })),
      },
      debugReport: this._debugger.getReport(),
    };
  }
}

module.exports = Battle;
