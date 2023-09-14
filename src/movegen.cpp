/*
  Stockfish, a UCI chess playing engine derived from Glaurung 2.1
  Copyright (C) 2004-2023 The Stockfish developers (see AUTHORS file)

  Stockfish is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.

  Stockfish is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program.  If not, see <http://www.gnu.org/licenses/>.
*/

#include "movegen.h"

#include <cassert>
#include <initializer_list>

#include "bitboard.h"
#include "position.h"

namespace Stockfish {

namespace {

  template<GenType Type, Direction D, bool Enemy>
  ExtMove* make_promotions(ExtMove* moveList, [[maybe_unused]] Square to) {

    if constexpr (Type == CAPTURES || Type == EVASIONS || Type == NON_EVASIONS)
    {
        *moveList++ = make<PROMOTION>(to - D, to, QUEEN);
        if constexpr (Enemy && Type == CAPTURES)
        {
            *moveList++ = make<PROMOTION>(to - D, to, ROOK);
            *moveList++ = make<PROMOTION>(to - D, to, BISHOP);
            *moveList++ = make<PROMOTION>(to - D, to, KNIGHT);
        }
    }

    if constexpr ((Type == QUIETS && !Enemy) || Type == EVASIONS || Type == NON_EVASIONS)
    {
        *moveList++ = make<PROMOTION>(to - D, to, ROOK);
        *moveList++ = make<PROMOTION>(to - D, to, BISHOP);
        *moveList++ = make<PROMOTION>(to - D, to, KNIGHT);
    }

    return moveList;
  }


  template<Color Us, GenType Type>
  ExtMove* generate_pawn_moves(const Position& pos, ExtMove* moveList, Bitboard target) {

    constexpr Color     Them     = ~Us;
    constexpr Bitboard  TRank7BB = (Us == WHITE ? Rank7BB    : Rank2BB);
    constexpr Bitboard  TRank3BB = (Us == WHITE ? Rank3BB    : Rank6BB);
    constexpr Direction Up       = pawn_push(Us);
    constexpr Direction UpRight  = (Us == WHITE ? NORTH_EAST : SOUTH_WEST);
    constexpr Direction UpLeft   = (Us == WHITE ? NORTH_WEST : SOUTH_EAST);

    const Bitboard emptySquares = ~pos.pieces();
    const Bitboard enemies      =  Type == EVASIONS ? pos.checkers()
                                                    : pos.pieces(Them);

    Bitboard pawnsOn7    = pos.pieces(Us, PAWN) &  TRank7BB;
    Bitboard pawnsNotOn7 = pos.pieces(Us, PAWN) & ~TRank7BB;

    // Single and double pawn pushes, no promotions
    if constexpr (Type != CAPTURES)
    {
        Bitboard b1 = shift<Up>(pawnsNotOn7)   & emptySquares;
        Bitboard b2 = shift<Up>(b1 & TRank3BB) & emptySquares;

        if constexpr (Type == EVASIONS) // Consider only blocking squares
        {
            b1 &= target;
            b2 &= target;
        }

        if constexpr (Type == QUIET_CHECKS)
        {
            // To make a quiet check, you either make a direct check by pushing a pawn
            // or push a blocker pawn that is not on the same file as the enemy king.
            // Discovered check promotion has been already generated amongst the captures.
            Square ksq = pos.square<KING>(Them);
            Bitboard dcCandidatePawns = pos.blockers_for_king(Them) & ~file_bb(ksq);
            b1 &= pawn_attacks_bb(Them, ksq) | shift<   Up>(dcCandidatePawns);
            b2 &= pawn_attacks_bb(Them, ksq) | shift<Up+Up>(dcCandidatePawns);
        }

        while (b1)
        {
            Square to = pop_lsb(b1);
            *moveList++ = make_move(to - Up, to);
        }

        while (b2)
        {
            Square to = pop_lsb(b2);
            *moveList++ = make_move(to - Up - Up, to);
        }
    }

    // Promotions and underpromotions
    if (pawnsOn7)
    {
        Bitboard b1 = shift<UpRight>(pawnsOn7) & enemies;
        Bitboard b2 = shift<UpLeft >(pawnsOn7) & enemies;
        Bitboard b3 = shift<Up     >(pawnsOn7) & emptySquares;

        if constexpr (Type == EVASIONS)
            b3 &= target;

        while (b1)
            moveList = make_promotions<Type, UpRight, true>(moveList, pop_lsb(b1));

        while (b2)
            moveList = make_promotions<Type, UpLeft, true>(moveList, pop_lsb(b2));

        while (b3)
            moveList = make_promotions<Type, Up,    false>(moveList, pop_lsb(b3));
    }

    // Standard and en passant captures
    if constexpr (Type == CAPTURES || Type == EVASIONS || Type == NON_EVASIONS)
    {
        Bitboard b1 = shift<UpRight>(pawnsNotOn7) & enemies;
        Bitboard b2 = shift<UpLeft >(pawnsNotOn7) & enemies;

        while (b1)
        {
            Square to = pop_lsb(b1);
            *moveList++ = make_move(to - UpRight, to);
        }

        while (b2)
        {
            Square to = pop_lsb(b2);
            *moveList++ = make_move(to - UpLeft, to);
        }

        if (pos.ep_square() != SQ_NONE)
        {
            assert(rank_of(pos.ep_square()) == relative_rank(Us, RANK_6));

            // An en passant capture cannot resolve a discovered check
            if (Type == EVASIONS && (target & (pos.ep_square() + Up)))
                return moveList;

            b1 = pawnsNotOn7 & pawn_attacks_bb(Them, pos.ep_square());

            assert(b1);

            while (b1)
                *moveList++ = make<EN_PASSANT>(pop_lsb(b1), pos.ep_square());
        }
    }

    return moveList;
  }


  template<Color Us, PieceType Pt, bool Checks>
  ExtMove* generate_moves(const Position& pos, ExtMove* moveList, Bitboard target) {

    static_assert(Pt != KING && Pt != PAWN, "Unsupported piece type in generate_moves()");

    Bitboard bb = pos.pieces(Us, Pt);

    while (bb)
    {
        Square from = pop_lsb(bb);
        Bitboard b = attacks_bb<Pt>(from, pos.pieces()) & target;

        // To check, you either move freely a blocker or make a direct check.
        if (Checks && (Pt == QUEEN || !(pos.blockers_for_king(~Us) & from)))
            b &= pos.check_squares(Pt);

        while (b)
            *moveList++ = make_move(from, pop_lsb(b));
    }

    return moveList;
  }


  template<Color Us, GenType Type>
  ExtMove* generate_all(const Position& pos, ExtMove* moveList) {

    static_assert(Type != LEGAL, "Unsupported type in generate_all()");

    constexpr bool Checks = Type == QUIET_CHECKS; // Reduce template instantiations
    const Square ksq = pos.square<KING>(Us);
    Bitboard target;

    // Skip generating non-king moves when in double check
    if (Type != EVASIONS || !more_than_one(pos.checkers()))
    {
        target = Type == EVASIONS     ?  between_bb(ksq, lsb(pos.checkers()))
               : Type == NON_EVASIONS ? ~pos.pieces( Us)
               : Type == CAPTURES     ?  pos.pieces(~Us)
                                      : ~pos.pieces(   ); // QUIETS || QUIET_CHECKS

        moveList = generate_pawn_moves<Us, Type>(pos, moveList, target);
        moveList = generate_moves<Us, KNIGHT, Checks>(pos, moveList, target);
        moveList = generate_moves<Us, BISHOP, Checks>(pos, moveList, target);
        moveList = generate_moves<Us,   ROOK, Checks>(pos, moveList, target);
        moveList = generate_moves<Us,  QUEEN, Checks>(pos, moveList, target);
    }

    if (!Checks || pos.blockers_for_king(~Us) & ksq)
    {
        Bitboard b = attacks_bb<KING>(ksq) & (Type == EVASIONS ? ~pos.pieces(Us) : target);
        if (Checks)
            b &= ~attacks_bb<QUEEN>(pos.square<KING>(~Us));

        while (b)
            *moveList++ = make_move(ksq, pop_lsb(b));

        if ((Type == QUIETS || Type == NON_EVASIONS) && pos.can_castle(Us & ANY_CASTLING))
            for (CastlingRights cr : { Us & KING_SIDE, Us & QUEEN_SIDE } )
                if (!pos.castling_impeded(cr) && pos.can_castle(cr))
                    *moveList++ = make<CASTLING>(ksq, pos.castling_rook_square(cr));
    }

    return moveList;
  }

} // namespace


/// <CAPTURES>     Generates all pseudo-legal captures plus queen promotions
/// <QUIETS>       Generates all pseudo-legal non-captures and underpromotions
/// <EVASIONS>     Generates all pseudo-legal check evasions when the side to move is in check
/// <QUIET_CHECKS> Generates all pseudo-legal non-captures giving check, except castling and promotions
/// <NON_EVASIONS> Generates all pseudo-legal captures and non-captures
///
/// Returns a pointer to the end of the move list.

template<GenType Type>
ExtMove* generate(const Position& pos, ExtMove* moveList) {

  static_assert(Type != LEGAL, "Unsupported type in generate()");
  assert((Type == EVASIONS) == (bool)pos.checkers());

  Color us = pos.side_to_move();

  return us == WHITE ? generate_all<WHITE, Type>(pos, moveList)
                     : generate_all<BLACK, Type>(pos, moveList);
}

// Explicit template instantiations
template ExtMove* generate<CAPTURES>(const Position&, ExtMove*);
template ExtMove* generate<QUIETS>(const Position&, ExtMove*);
template ExtMove* generate<EVASIONS>(const Position&, ExtMove*);
template ExtMove* generate<QUIET_CHECKS>(const Position&, ExtMove*);
template ExtMove* generate<NON_EVASIONS>(const Position&, ExtMove*);


/// generate<LEGAL> generates all the legal moves in the given position

// template<>
// ExtMove* generate<LEGAL>(const Position& pos, ExtMove* moveList) {

//   Color us = pos.side_to_move();
//   Bitboard pinned = pos.blockers_for_king(us) & pos.pieces(us);
//   Square ksq = pos.square<KING>(us);
//   ExtMove* cur = moveList;

//   moveList = pos.checkers() ? generate<EVASIONS    >(pos, moveList)
//                             : generate<NON_EVASIONS>(pos, moveList);
//   while (cur != moveList)
//       if (  ((pinned & from_sq(*cur)) || from_sq(*cur) == ksq || type_of(*cur) == EN_PASSANT)
//           && !pos.legal(*cur))
//           *cur = (--moveList)->move;
//       else
//           ++cur;

//   return moveList;
// }

//generate attacks
template<Color attacker>
    constexpr Bitboard generate_attacks(const Position& pos){
        //slider attacks should go through king
        Bitboard occupancy = pos.pieces() & ~pos.pieces(~attacker, KING);

        Bitboard attacks = pawn_attacks_bb<attacker>(pos.pieces(attacker, PAWN));
        attacks |= attacks_bb<KING>(pos.square<KING>(attacker));

        Bitboard bb = pos.pieces(attacker, KNIGHT);
        while (bb){
            attacks |= attacks_bb<KNIGHT>(pop_lsb(bb));
        }
        bb = pos.pieces(attacker, ROOK, QUEEN);
        while (bb){
            attacks |= attacks_bb<ROOK>(pop_lsb(bb), occupancy); 
        }
        bb = pos.pieces(attacker, BISHOP, QUEEN);
        while (bb){
            attacks |= attacks_bb<BISHOP>(pop_lsb(bb), occupancy);
        }
        return attacks;
    }

//legal movegen
template<Color Us>
ExtMove* generate_legal(const Position& pos, ExtMove* moveList) {
    constexpr Color Them = ~Us;
    constexpr Direction Up = pawn_push(Us);

    Square sq;
    Bitboard bb, attacks;

    const Square ksq = pos.square<KING>(Us);
    const Bitboard theirAttacks = generate_attacks<Them>(pos);

    attacks = attacks_bb<KING>(ksq) & ~pos.pieces(Us) & ~theirAttacks;

    while (attacks)
        *moveList++ = make_move(ksq, pop_lsb(attacks));

    if (popcount(pos.checkers()) > 1) return moveList;

    const Bitboard checkMask = pos.checkers() ? between_bb(ksq, lsb(pos.checkers())) : ~0ull;
    const Bitboard them = pos.pieces(Them) & checkMask;
    const Bitboard occ = pos.pieces(); //occupancy

    //find rook pins and bishop pins
    Bitboard rpins = attacks_bb<ROOK  >(ksq) & pos.pinners(Them);
    Bitboard rpinMask = 0ull;
    while (rpins)
        rpinMask |= between_bb(ksq, pop_lsb(rpins));

    Bitboard bpins = attacks_bb<BISHOP>(ksq) & pos.pinners(Them);
    Bitboard bpinMask = 0ull;
    while (bpins)
        bpinMask |= between_bb(ksq, pop_lsb(bpins));
    
    const Bitboard unpinned = ~(bpinMask | rpinMask);

    //castling, not available for 960 for now
    if (!pos.checkers() && pos.can_castle(Us & ANY_CASTLING)){
        constexpr CastlingRights crk = Us & KING_SIDE;
        constexpr CastlingRights crq = Us & QUEEN_SIDE;

        if (!pos.castling_impeded(crk) && pos.can_castle(crk))
            if (!(theirAttacks & (Us == WHITE ? SQ_F1 | SQ_G1 : SQ_F8 | SQ_G8)))
                *moveList++ = make<CASTLING>(ksq, pos.castling_rook_square(crk));

        if (!pos.castling_impeded(crq) && pos.can_castle(crq))
            if (!(theirAttacks & (Us == WHITE ? SQ_D1 | SQ_C1 : SQ_D8 | SQ_C8)))
                *moveList++ = make<CASTLING>(ksq, pos.castling_rook_square(crq));
    }

    if (pos.ep_square() != SQ_NONE
    // && pawn_attacks_bb(Them, pos.ep_square()) & pos.pieces(Us, PAWN) //should already be checked for when making move
    && checkMask & (pos.ep_square() - Up)){
        const Square capsq = pos.ep_square() - Up;

        //horizontal rook attacks "seeing through" ep captured pawn
        Bitboard eppin = attacks_bb<ROOK>(ksq, occ ^ capsq) & pos.pieces(Us);
        eppin = attacks_bb<ROOK>(ksq, (occ & ~eppin) ^ capsq) & pos.pieces(Them, ROOK, QUEEN) & rank_bb(ksq);

        //ensure pinner rook is aligned with ray cast from king, can definitely be precomputed into an array like ray[ksq][left/right]
        eppin &= attacks_bb<ROOK>(ksq) & attacks_bb<ROOK>(capsq, square_bb(ksq));

        const Bitboard eppinMask = eppin ? between_bb(ksq, pop_lsb(eppin)) : 0; //only one possible horizontal rook ep pin at a time
        
        //ep pawn can only be captured by us if it's not pinned / pinned vertically
        //and our own pawn can't capture if it's pinned by a rook
        if (!((bpinMask | eppinMask) & capsq)){
            bb = pawn_attacks_bb(Them, pos.ep_square()) & pos.pieces(Us, PAWN) & unpinned;
            while (bb)
                *moveList++ = make<EN_PASSANT>(pop_lsb(bb), pos.ep_square());
        }
    }

    constexpr Direction UpRight  = Us == WHITE ? NORTH_EAST : SOUTH_WEST;
    constexpr Direction UpLeft   = Us == WHITE ? NORTH_WEST : SOUTH_EAST;
    constexpr Bitboard rank7R = Us == WHITE ? Rank7BB : Rank2BB; //relative rank 7
    constexpr Bitboard rank3R = Us == WHITE ? Rank3BB : Rank6BB; //relative rank 3
    const Bitboard rpinMask_h = rpinMask & rank_bb(ksq); //horizontal pins
    const Bitboard emptySquares = ~occ;
    const Bitboard notUs = ~pos.pieces(Us);
    const Bitboard pawnsOn7    = pos.pieces(Us, PAWN) &  rank7R;
    const Bitboard pawnsNotOn7 = pos.pieces(Us, PAWN) & ~rank7R;

    Bitboard piece_bb;

    if (pawnsOn7)
    {
        //unpinned promotion captures
        Bitboard b1 = shift<UpRight>(pawnsOn7 & unpinned) & them;
        Bitboard b2 = shift<UpLeft >(pawnsOn7 & unpinned) & them;

        while (b1)
            moveList = make_promotions<CAPTURES, UpRight, true>(moveList, pop_lsb(b1));

        while (b2)
            moveList = make_promotions<CAPTURES, UpLeft, true>(moveList, pop_lsb(b2));

        //pinned promotion captures
        Bitboard b3 = pawnsOn7 & bpinMask & ~rpinMask;
        b1 = shift<UpLeft >(b3) & them & bpinMask;
        b1 = shift<UpRight>(b3) & them & bpinMask;

        while (b1)
            moveList = make_promotions<CAPTURES, UpRight, true>(moveList, pop_lsb(b1));

        while (b2)
            moveList = make_promotions<CAPTURES, UpLeft, true>(moveList, pop_lsb(b2));

        //push promotion, pinned pawns cannot push promote
        b3 = shift<Up>(pawnsOn7 & unpinned) & emptySquares & checkMask;

        while (b3)
            moveList = make_promotions<NON_EVASIONS, Up,    false>(moveList, pop_lsb(b3));
    }

    //unpined normal captures
    bb = shift<UpLeft>(pawnsNotOn7 & unpinned) & them;
    while (bb){
        sq = pop_lsb(bb);
        *moveList++ = make_move(sq - UpLeft, sq);
    }
    bb = shift<UpRight>(pawnsNotOn7 & unpinned) & them;
    while (bb){
        sq = pop_lsb(bb);
        *moveList++ = make_move(sq - UpRight, sq);
    }

    //pinned normal captures
    piece_bb = pawnsNotOn7 & bpinMask & ~rpinMask;
    bb = shift<UpLeft>(piece_bb) & them & bpinMask;
    while (bb){
        sq = pop_lsb(bb);
        *moveList++ = make_move(sq - UpLeft, sq);
    }
    bb = shift<UpRight>(piece_bb) & them & bpinMask;
    while (bb){
        sq = pop_lsb(bb);
        *moveList++ = make_move(sq - UpRight, sq);
    }

    //pawn push, those pinned by bishop / horizontal rook cannot push
    //single push
    piece_bb = shift<Up>(pawnsNotOn7 & ~bpinMask & ~rpinMask_h) & emptySquares;
    bb = piece_bb & checkMask;
    while (bb){
        sq = pop_lsb(bb);
        *moveList++ = make_move(sq - Up, sq);
    }

    //double push
    bb = shift<Up>(piece_bb & rank3R) & emptySquares & checkMask;
    while (bb){
        sq = pop_lsb(bb);
        *moveList++ = make_move(sq - Up - Up, sq);
    }

    //knight moves, pinned knights can't move
    bb = pos.pieces(Us, KNIGHT) & unpinned;
    while (bb){
        sq = pop_lsb(bb);
        attacks = attacks_bb<KNIGHT>(sq) & notUs & checkMask;
        while (attacks)
            *moveList++ = make_move(sq, pop_lsb(attacks));
    }

    //unpinned bishop moves
    piece_bb = pos.pieces(Us, BISHOP, QUEEN);
    bb = piece_bb & unpinned;
    while (bb){
        sq = pop_lsb(bb);
        attacks = attacks_bb<BISHOP>(sq, occ) & notUs & checkMask;
        while (attacks)
            *moveList++ = make_move(sq, pop_lsb(attacks));
    }

    //pinned bishop moves
    //we only need to check for bishop pins, since a piece cannot be pinned by both bishop and rook at the same time
    bb = piece_bb & bpinMask;
    while (bb){
        sq = pop_lsb(bb);
        attacks = attacks_bb<BISHOP>(sq, occ) & notUs & checkMask & bpinMask;
        while (attacks)
            *moveList++ = make_move(sq, pop_lsb(attacks));
    }

    //unpinned rook moves
    piece_bb = pos.pieces(Us, ROOK, QUEEN);
    bb = piece_bb & unpinned;
    while (bb){
        sq = pop_lsb(bb);
        attacks = attacks_bb<ROOK>(sq, occ) & notUs & checkMask;
        while (attacks)
            *moveList++ = make_move(sq, pop_lsb(attacks));
    }

    //pinned rook moves, same logic
    bb = piece_bb & rpinMask;
    while (bb){
        sq = pop_lsb(bb);
        attacks = attacks_bb<ROOK>(sq, occ) & notUs & checkMask & rpinMask;
        while (attacks)
            *moveList++ = make_move(sq, pop_lsb(attacks));
    }

    return moveList;
}

template<>
ExtMove* generate<LEGAL>(const Position& pos, ExtMove* moveList) {
    return pos.side_to_move() == WHITE ?  generate_legal<WHITE>(pos, moveList)
                                        : generate_legal<BLACK>(pos, moveList);
}


} // namespace Stockfish
