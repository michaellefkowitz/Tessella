# -*- coding: utf-8 -*-
"""
Created on Mon Feb 02 19:49:28 2015

@author: Michael

This file contains game logic, game AI, and a graphical gameplay system
for the game Tessella. 

The graphical componenet uses pygames.py.

"""

from __future__ import division # / returns reals when applied to two ints. use // for integer division now.
import os.path
import operator, sys, pickle
import random
import pygame
from pygame.locals import *

import cProfile, pstats, StringIO

infinity = 1.0e400

##############
# GAME LOGIC #
##############

cardinal_directions = set([(1,0),(-1,0),(0,1),(0,-1)])
diagonal_directions = set([(1,1),(-1,1),(1,-1),(-1,-1)])
directions = set.union(cardinal_directions, diagonal_directions)
        
class Tessella:
    
    def __init__(self, dimensions):
        self.savefile = "savedmoves" + str(dimensions) + ".p"
        self.researchfile = "toresearch" + str(dimensions) + ".p"
        self.d = dimensions
        self.h = self.d * 2 - 1
        self.pieces_remaining = {-1: self.h-2, 1: self.h-2}
        
        # Store locations of octagons, squares, all spaces in sets
        self.octs = set()
        self.squares = set()
        self.tiles = set()
        for r in range(self.h):
            for c in range(self.h):
                if abs(self.d - r - 1) + abs(self.d - c - 1) < self.d:
                    if (r + c) % 2 == self.d % 2:
                        self.squares.add((r,c))
                    else:
                        self.octs.add((r,c))
                    self.tiles.add((r,c))
        
        # Store what neighboring locations each tile has in a dictionary of sets
        self.neighbors = {}
        for r in range(self.h):
            for c in range(self.h):
                if (r,c) in self.tiles:
                    ns = set()
                    for direction in cardinal_directions if (r,c) in self.squares else directions:
                        n = tuple(map(operator.add, (r,c), direction))
                        if n in self.tiles:
                            ns.add(n)
                    self.neighbors[(r,c)] = ns
        
        # Store which pairs of tiles are aligned, what tiles intervene (set), and what they're attacking (in list and set form)
        self.aligned = {}
        for (r,c) in self.tiles:         # from
            for (rr,cc) in self.tiles:   # to
                if (r,c) != (rr,cc):
                    dr = rr - r # direction in row dimension (-1,0,1)
                    dc = cc - c # direction in col dimension (-1,0,1)
                    if abs(dc) == abs(dr) or dr * dc == 0:
                        intermediate = []
                        attacked = []
                        dr, dc = cmp(dr,0), cmp(dc,0)
                        sr, sc = r + dr, c + dc             # selected tile moves from backer towards piece
                        while (sr,sc) != (rr,cc):           # before hitting attacking piece
                            intermediate.append((sr,sc))    # add to list of intermediate tiles
                            sr, sc = sr+dr, sc+dc           # move to next tile
                        sr, sc = sr+dr, sc+dc
                        while (sr,sc) in self.tiles:        # before hittin board edge
                            attacked.append((sr,sc))        # add to list of attacked tiles
                            sr, sc = sr+dr, sc+dc           # move to next tile
                        if attacked:
                            self.aligned[((r,c),(rr,cc))] = set(intermediate), attacked, set(attacked)

        # Create initial state
        friendly = set()
        enemy = set()
        for i in range(1,self.h-1):
            enemy.add((abs(self.d-i-1), i))
            friendly.add((self.h - 1 - abs(self.d-i-1), i))
        self.initial = {"player":1,"pieces":{1: friendly, -1: enemy, 0: friendly.union(enemy)},"ply":0}
        
        # Remember best moves of already seen board positions (speed up opengame)
        # states seen in human player games (to research later), and killer moves per depth
        self.best_moves = {}
        self.to_research = []
        self.killer_moves = {}
        self.killer_memory = 3
        
        # ASCII symbols to use when printing the board
        self.symbols = {1:"o", -1:"x", "oct":'-', "square":".", None:" "}
        
    def display(self, state):
        '''prints the board to the shell'''
        line = ' '
        for c in range(self.h):
            line += ' ' + str(c)
        for r in range(self.h):
            line += '\n' + str(r)
            for c in range(self.h):
                line += ' '
                if (r,c) in state["pieces"][1]:
                    line+= self.symbols[1]
                elif (r,c) in state["pieces"][-1]:
                    line+= self.symbols[-1]
                elif (r,c) in self.octs:
                    line+= self.symbols["oct"]
                elif (r,c) in self.squares:
                    line+= self.symbols["square"]    
                else:
                    line+= self.symbols[None]
            line += ' ' + str(r)
        line += '\n '
        for c in range(self.h):
            line += ' ' + str(c)        
        print line + '\n'
        
    def result(self,state,move):
        '''takes a state and a proposed move, and returns the new
        state after the move has occured'''
        
        ((r,c),(rr,cc)) = move
        player = state["player"]
        
        # Make a copy of the old state
        #newstate = copy.deepcopy(state)
        newstate = dict(state)
        newstate["pieces"] = dict(newstate["pieces"])
        for key in newstate["pieces"]:
            newstate["pieces"][key] = set(newstate["pieces"][key])

        # Pick up piece
        newstate["pieces"][player].remove((r,c))     
        newstate["pieces"][0].remove((r,c))     
        # Remove captured piece if any
        newstate["pieces"][-player].discard((rr,cc))
        newstate["pieces"][0].discard((rr,cc))
        # Place at new location
        newstate["pieces"][player].add((rr,cc))    
        newstate["pieces"][0].add((rr,cc))
        
        # Switch players
        newstate["player"] = -player
        # Increase game depth
        newstate["ply"] += 1
        
        return newstate
        
    def step_moves(self,state):
        '''returns the list of legal step moves'''
        moves = []
        all_pieces = state["pieces"][0]

        for piece in state["pieces"][state["player"]]:
            moves += [(piece,neighbor) for neighbor in self.neighbors[piece] if not (neighbor in all_pieces)]
        return moves
    
    
    def capture_moves(self,state): 
        '''returns the list of legal capturing moves'''
        moves = []
        player = state["player"]
        all_pieces = state["pieces"][0]
        
        # Loop over all attacker / backer pairs of friendly pieces
        for attacker in state["pieces"][player]:
            for backer in state["pieces"][player]:
                if (backer,attacker) in self.aligned:                                          # if the pieces are in a line,
                    if state["pieces"][-state["player"]] & self.aligned[(backer,attacker)][2]: # if some enemy piece is in the line of fire (saves time)
                        if not all_pieces & self.aligned[(backer,attacker)][0]:                # if there are no interveners,
                            # check through attacked tiles, in order
                            for attacked_spot in self.aligned[(backer,attacker)][1]:  
                                if attacked_spot in state["pieces"][state["player"]]:
                                    break
                                if attacked_spot in state["pieces"][-state["player"]]:
                                    moves.append((attacker,attacked_spot))
                                    break
        return moves
    
    # Additional functions for the games.py module
    def actions(self, state):
        "Return a list of the allowable moves at this point."
        if self.terminal_test(state):
            return []
        else:
            return self.capture_moves(state) + self.step_moves(state)
    
    def spread(self, points):
        '''Returns sum of horizontal distance from horizontal average'''
        avgx = sum(x for (x,y) in points) / len(points)
        #avgy = sum(y for (x,y) in points) / len(points)
        xerr = sum(abs(x - avgx) for (x,y) in points)
        #yerr = sum(abs(y - avgy) for (x,y) in points)
        return xerr #+ yerr
    
    def periferality(self, points):
        '''Returns sum of horizontal and vertical distances from center'''
        return sum((abs(x - self.d + 1) + abs(y - self.d + 1)) for (x,y) in points)
        
    def utility(self, state, player):
        '''Return the value to current player, which is made of five factors
        of decreasing importance: w
        1. whether the player has won,
        2. the piece count, 
        3. how clustered the players pieces are
        4. how central the pieces are,
        5. a random  noise factor
        '''
        
        mine, yours = state["pieces"][player], state["pieces"][-player]
        
        win_points = (len(yours) == self.d - 2) - (len(mine) == self.d - 2)
        pieces_points = len(mine) - len(yours)
        
        if win_points:
            return win_points * 1000 + pieces_points
   
        clustered_points = self.spread(yours) - self.spread(mine)
        centrality_points = self.periferality(yours) - self.periferality(mine)
        
        return int(50 * pieces_points + 2 * clustered_points + centrality_points)
    
    def terminal_test(self, state):
        '''A state is terminal if one player has fewer than d - 1 pieces'''
        return (len(state["pieces"][-1]) < self.d-1) or (len(state["pieces"][1]) < self.d-1)
        
    def freeze_state(self, s): # make a hashable version of the state, for use in lookup table    
        return (frozenset(s["pieces"][s["player"]]), frozenset(s["pieces"][-s["player"]]))
    
    def thaw_state(self, fs, player=1,ply=0):
        state = {"player":player, "ply":ply}
        mine, yours = fs
        mine, yours = set(mine), set(yours)
        state["pieces"] = {player:mine,-player:yours}
        return state       
       
    def save_moves(self, state, bestmoves):
        '''for eight frozen states symmetrical to s, saves the ideal moves supplied'''
        def flip(n):
            return 2 * (self.d - 1) - n
        mine, yours = state["pieces"][state["player"]], state["pieces"][-state["player"]]
        flips = [lambda (r,c): (r, c),
                 lambda (r,c): (flip(r), c),
                 lambda (r,c): (flip(r), flip(c)),
                 lambda (r,c): (r, flip(c))]
        for f in flips:
            self.best_moves[(frozenset(map(f,mine)),frozenset(map(f,yours)))] = map(lambda x: tuple(map(f,x)), bestmoves)
        return
        
    def load_best_moves(self):
        '''replace best moves dictionary with contents of pickled file'''
        self.best_moves = pickle.load( open( self.savefile, "rb" ) )
        self.to_research = pickle.load( open( self.researchfile, "rb" ) )
        
    def dump_best_moves(self):
        '''save best move to pickle file'''
        pickle.dump( self.best_moves, open( self.savefile, "wb" ) )
        pickle.dump( self.to_research, open( self.researchfile, "wb" ) )
        
    def get_random_state(self, whites, blacks):
        state = {}
        state["player"] = random.choice([-1,1])
        state["ply"] = 0
        state["pieces"] = {1:set(), -1:set(), 0:set()}
        
        lastrow = (self.d - 1) * 2
        w = b = 0
        while w < whites:
            r, c = random.randint(0,lastrow), random.randint(0,lastrow)
            if (r,c) in self.tiles and (r,c) not in state["pieces"][1]:
                state["pieces"][1].add((r,c))
                state["pieces"][0].add((r,c))
                w += 1
        while b < blacks:
            r, c = random.randint(0,lastrow), random.randint(0,lastrow)
            if (r,c) in self.tiles and (r,c) not in state["pieces"][1] and (r,c) not in state["pieces"][-1]:
                state["pieces"][-1].add((r,c))
                state["pieces"][0].add((r,c))
                b += 1
        assert state["pieces"][0] == state["pieces"][-1].union(state["pieces"][1])
        return state
                
###########
# GAME AI #
###########

def alphabeta_tessella_search(state, game, mindepth=3, maxdepth=6, drawstates={}, storebest=False, noise=0.0, lookupbest=True):
    """Search game to determine best action; use alpha-beta pruning.
    This version cuts off search and uses an evaluation function when
    it reaches max depth, and only considers capture moves after min depth."""
    player = state["player"]   
    ply = state["ply"]
    
    def max_value(state, alpha, beta, depth):
        frozenstate = game.freeze_state(state)
        
        # Use value of best move if stored alerady
        if frozenstate in game.best_moves:
            return game.best_moves[frozenstate][1] * (1 + random.random() * noise)
            
        # Terminate and use utility if bottoming out
        if depth > maxdepth or game.terminal_test(state):
            if frozenstate in drawstates and drawstates[frozenstate] >= 2:
                return 0
            else:
                return game.utility(state, player)
        captures = game.capture_moves(state)
        if depth > mindepth and not captures:
            if frozenstate in drawstates and drawstates[frozenstate] >= 2:
                return 0
            else:
                return game.utility(state, player)
                
        # Recurse on all available actions, or just captures
        actions = captures
        if depth <= mindepth:
            actions += game.step_moves(state)
        v = -infinity
        
        # Use killer heuristic to sort moves
        p = depth + ply
        if p in game.killer_moves:
            try_first = game.killer_moves[p]
            actions.sort(key=(try_first+actions).index)
        else:
            game.killer_moves[p] = [None for i in range(game.killer_memory)]
            
        # Main body
        for a in actions:
            newv = min_value(game.result(state, a), alpha, beta, depth+1)
            v = max(v, newv)
            if v >= beta:
                if not a in game.killer_moves[p]:
                    game.killer_moves[p] = [a] + game.killer_moves[p][:-1]
                return v
            alpha = max(alpha, v)
        return v * (1 + random.random() * noise)

    def min_value(state, alpha, beta, depth):
        frozenstate = game.freeze_state(state)
        
        # Use value of best move if stored alerady
        if frozenstate in game.best_moves:
            return game.best_moves[frozenstate][1] * (1 + random.random() * noise)
            
        # Terminate and use utility if bottoming out
        if depth > maxdepth or game.terminal_test(state):
            if frozenstate in drawstates and drawstates[frozenstate] >= 2:
                return 0
            else:
                return game.utility(state, player)
        captures = game.capture_moves(state)
        if depth > mindepth and not captures:
            if frozenstate in drawstates and drawstates[frozenstate] >= 2:
                return 0
            else:
                return game.utility(state, player)
                
        # Recurse on all available actions, or just captures
        actions = captures
        if depth <= mindepth:
            actions += game.step_moves(state)
        v = infinity       
        
        # Use killer heuristic to sort moves
        p = depth + ply
        if p in game.killer_moves:
            try_first = game.killer_moves[p]
            actions.sort(key=(try_first+actions).index)
        else:
            game.killer_moves[p] = [None for i in range(game.killer_memory)]  
            
        # Main body
        for a in actions:
            newv = max_value(game.result(state, a), alpha, beta, depth+1)
            v = min(v, newv)
            if v <= alpha:
                if not a in game.killer_moves[p]:
                    game.killer_moves[p] = [a] + game.killer_moves[p][:-1] #
                return v
            beta = min(beta, v)
        return v * (1 + random.random() * noise)
    
    # Body of search starts here
    bestmoves = []
    bestvalue = -infinity
    
    # Use one of best moves if stored alerady    
    frozenstate = game.freeze_state(state)
    if lookupbest and frozenstate in game.best_moves:
        move = random.choice(game.best_moves[frozenstate][0])
        print "looked up best moves (", len(game.best_moves[frozenstate][0]), ")"
        return move
    
    # Sort moves using killer heuristic
    actions = game.actions(state)
    if ply in game.killer_moves:
        actions.sort(key=(game.killer_moves[ply]+actions).index)
    
    # Check every move
    for move in actions:
        print "testing move", move, "...", # useful to diagnose ordering hueristics
        result = game.result(state, move)
        
        # Terminate if a move that wins immediately is found
        if game.terminal_test(result):
            bestmoves = [move]
            val = game.utility(result, player)
            break
        val = min_value(result,-infinity,infinity,0)
        print round(val,2)
        '''
        # Any winning branch will do, stop searching if one is found
        if val > 1000:   ######
            print ""     ######
            return move  ######
        '''
        if val > bestvalue:
            bestmoves = [move]
            bestvalue = val
        elif val == bestvalue:
            bestmoves.append(move)
    print ""
    
    if storebest:
        game.best_moves[game.freeze_state(state)] = (bestmoves, val) # Store solution for future use in move ordering
    if len(bestmoves) > 1:
        print len(bestmoves), "moves tied for best move."
    return random.choice(bestmoves)



###############
### PLAYERS ###
###############

def query_player(game, state):
    while True:
        s = raw_input('Your move: Type four numbers seperated by spaces: ')
        try:
            a,b,c,d = [int(i) for i in s.split(' ')]
            if ((a,b),(c,d)) in game.actions(state):
                return ((a,b),(c,d))
            else:
                print "That's not a legal move."
        except:
            print "That's not the right format."
            
def captury_player(game, state, drawstates={}):
    print "capturing player:"
    if game.capture_moves(state):
        return random.choice(game.capture_moves(state))
    else:
        return random.choice(game.step_moves(state))

def random_player(game, state, drawstates={}, verbose=True):
    move = random.choice(game.actions(state))
    if verbose:
        print "random player:", move, "\n"
    return move
    
def meh_stoch_player(game, state, drawstates={}, verbose=True):
    player = state["player"]
    moves = []
    totalutil = 0
    for action in game.actions(state):
        util = game.utility(game.result(state,action),player)
        moves.append((action, util))
        totalutil += util
    choice = random.random() * totalutil
    for move in moves:
        totalutil -= move[1]
        if totalutil <= choice:
            if verbose:
                print "meh stochastic player:", move[0], "\n"
            return move[0]
    return moves[0][0] # In case the above runs out of moves...which it shouldnt...

def great_ab_player(game, state, drawstates={}):
    print "great ab player:"
    move = alphabeta_tessella_search(state, game, 4, 10, drawstates, storebest=True)
    print move, "\n"
    return move


def safe_great_ab_player(game, state, drawstates={}):
    print "great ab player:"
    move = alphabeta_tessella_search(state, game, 4, 10, drawstates, storebest=False, lookupbest=False)
    print move, "\n"
    return move

def ab_player(game, state, drawstates={}):
    print "ab player:"
    move = alphabeta_tessella_search(state, game, 3, 10, drawstates)
    print move, "\n"
    return move
    
def noisy_ab_player(game, state, drawstates={}):
    print "noisy ab player:"
    move = alphabeta_tessella_search(state, game, 3, 10, drawstates, lookupbest=False, noise=0.2)
    print move, "\n"
    return move
    
def faulty_ab_player(game, state, drawstates={}):
    print "faulty ab player:"
    r = random.random()
    if r * (state["ply"] // 2 + 2) < .7 :
        print "oops!"
        return random_player(game, state)    
    else:
        return ab_player(game, state, drawstates)

    
def fast_ab_player(game, state, drawstates={}):
    print "fast ab player:"
    move = alphabeta_tessella_search(state, game, 2, 8, drawstates, lookupbest=False)
    print move, "\n"
    return move

##########################
# GAME PLAY IN TERMINAL #
##########################

def play_game(game, *players):
    """Play an n-person, move-alternating game.
    >>> play_game(Fig52Game(), alphabeta_player, alphabeta_player)
    3
    """
    
    used_states = {}
    
    state = game.initial
    
    i = 0
    game.display(state)
    
    while True:
        i += 1
        for player in players:
            move = player(game, state)
            state = game.result(state, move)
            
            # Print board
            print "(",i,")",'\n'
            game.display(state) 
            
            if game.terminal_test(state):
                return game.utility(state, 1)
            
            frozen_state = game.freeze_state(state) 
            
            if frozen_state in used_states:
                used_states[frozen_state] += 1
                if used_states[frozen_state] == 3:
                    print "Draw by threefold repetition."
                    return 0
            else:
                used_states[frozen_state] = 1



#####################
# GRAPHIC GAME PLAY #
#####################

board_offset = 141, 143
tile_size = 74 # Distance between centers of adjacent tiles
piece_r = 30

black = 0, 0, 0
white = 255,255,255
gray = 130,130,130
blueish = 70, 70, 180
red = 200,0,0
trans = 0,201,201

# Get photos 
board_img = pygame.image.load("board.png")
board_4_img = pygame.image.load("board4.png")
board_6_img = pygame.image.load("board6.png")

darkpiece_img = pygame.image.load("dpiece.png")
lightpiece_img = pygame.image.load("lpiece.png")



def get_board_position((xreal,yreal)):
    '''determine what tile a point on the screen is on'''
    c = (xreal - board_offset[0]) / tile_size + 0.5
    r = (yreal - board_offset[1]) / tile_size + 0.5
    return (int(r),int(c))

def get_real_position((r,c)): 
    '''get screen location of center point of tile on board'''
    xreal = c * tile_size + board_offset[0]
    yreal = r * tile_size + board_offset[1]
    return (xreal,yreal)

def play_gui_game(game, p1_humanity, p2_humanity, ai1=None, ai2=None, lencap=None, alternate=False, delay=700, single_game=False):
    
    # Load best moves, research dict from pickled files
    if os.path.isfile(game.savefile):
        game.best_moves = pickle.load( open( game.savefile, "rb" ) )
    if os.path.isfile(game.researchfile):
        game.to_research = pickle.load( open( game.researchfile, "rb" ) )
    
    # Which players are humans? What AI should the computers be?
    humanity = {1: p1_humanity, -1: p2_humanity}
    ai = {1: ai1}
    if ai2:
        ai[-1] = ai2
    else:
        ai[-1] = ai1
    
    # Start up pygames
    pygame.init()
    
    # Choose a board
    if game.d == 4:
        board = board_4_img
    elif game.d == 5:
        board = board_img
    elif game.d == 6:
        board = board_6_img
    boardrect = board.get_rect()
    size = width, height = boardrect.size
    
    # Make a screen surface
    screen = pygame.display.set_mode(size)
    
    # Create font objects
    bigfont = pygame.font.Font(None, 70)
    go_text = bigfont.render("GAME OVER", 0, red)
    (w,h) = go_text.get_size()
    (ww,hh) = size
    text_pos = (ww-w)//2, (hh-h)//2

    font = pygame.font.Font(None, 30)
    thinking_text = font.render("Computer thinking...", 0, white)
    
    # Initialize game state
    state = game.initial
    
    # GUI specific game state variables
    being_dragged = None
    vacated_spot = None
    last_moved_spot = None
    game_over = False
    
    def draw_everything():
        # Draw background, board          
        screen.fill(black)
        screen.blit(board, boardrect)
        
        # Draw the last moved and vacated circles
        if vacated_spot:
            line_surface = pygame.Surface(size)
            line_surface.set_colorkey(trans)
            line_surface.fill(trans)
            line_surface.set_alpha(100)

            pygame.draw.line(line_surface, white, last_moved_spot, vacated_spot, 12)
            pygame.draw.circle(line_surface, white, vacated_spot, piece_r // 2)
            
            #pygame.draw.line(line_surface, trans, last_moved_spot, vacated_spot, 6)
            #pygame.draw.circle(line_surface, trans, vacated_spot, piece_r // 2 - 3)
            pygame.draw.circle(line_surface, trans, last_moved_spot, piece_r - 2)
            
            
            screen.blit(line_surface, (0,0))

        # Draw the pieces
        d = piece_r*2
        for piece in state["pieces"][-1]:
            if piece != being_dragged:
                x,y = get_real_position(piece)
                screen.blit(darkpiece_img, (x-piece_r, y-piece_r, d, d))
        for piece in state["pieces"][1]:
            if piece != being_dragged:
                x,y = get_real_position(piece)
                screen.blit(lightpiece_img, (x-piece_r, y-piece_r, d, d))
        if being_dragged:
            x,y = pygame.mouse.get_pos()
            if being_dragged in state["pieces"][-1]:
                screen.blit(darkpiece_img, (x-piece_r, y-piece_r, d, d))
            else:
                screen.blit(lightpiece_img, (x-piece_r, y-piece_r, d, d))
        
        # Draw captured pieces on sidelines
        blacks_taken = game.h - 2 - len(state["pieces"][-1])
        whites_taken = game.h - 2 - len(state["pieces"][1])
        x = size[0] - 3 * piece_r
        y = piece_r
        for b in range(blacks_taken):
            screen.blit(darkpiece_img, (x, y, d, d))
            y += 1.5 * piece_r
        y = size[1] - 3 * piece_r
        for w in range(whites_taken):
            screen.blit(lightpiece_img, (x, y, d, d))
            y -= 1.5 * piece_r
        
        # Draw GAME OVER text, thinking text
        if game_over:
            screen.blit(go_text, text_pos)
        if not humanity[state["player"]]:
            screen.blit(thinking_text, (20,20))
        
        pygame.display.flip()
    
    # Main loop
    draw_everything()
    used_states = {}
    previous_human_states = [] # A stack
    
    while True:

        # Let machine move (screen is frozen during this time)
        if not humanity[state["player"]] and not game_over:
            pygame.time.wait(delay) # don't move instantly; wait 300 ms
            move = ai[state["player"]](game, state, used_states)
            state = game.result(state, move)
            vacated_spot = get_real_position(move[0])
            last_moved_spot = get_real_position(move[1])
            frozen_state = game.freeze_state(state)
            
            # If there's a human player, research this state later
            if (not game.terminal_test(state)) and (p1_humanity or p2_humanity) and state["ply"] <= 10:
                game.to_research.append(frozen_state)
            
            if frozen_state in used_states:
                used_states[frozen_state] += 1   
                if used_states[frozen_state] >= 3:
                    print "Draw by threefold repetition."
                    game_over = True

            else:
                used_states[frozen_state] = 1
            
            #####
            if lencap and state["ply"] >= lencap:
                game_over = True
            #####                
                
        # Let humans move / interact by listening for events
        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                sys.exit()
            
            # Mouse click logic
            elif event.type == pygame.MOUSEBUTTONDOWN and not game_over:
                if event.button == 1: # Left click
                    clicked = get_board_position(pygame.mouse.get_pos())
                    if clicked in state["pieces"][state["player"]]:
                        being_dragged = clicked
            elif event.type == pygame.MOUSEBUTTONDOWN and game_over:
                    game_over = False
                    state = game.initial
                    previous_human_states = []
                    being_dragged = None
                    vacated_spot = None
                    last_moved_spot = None
            elif event.type == pygame.MOUSEBUTTONUP:
                if event.button == 1: # Left click
                    if being_dragged:
                        dropped = get_board_position(pygame.mouse.get_pos())
                        move = (being_dragged,dropped)
                        if move in game.actions(state):
                            previous_human_states.append(state)
                            state = game.result(state, move)
                            vacated_spot = get_real_position(move[0])
                            last_moved_spot = get_real_position(move[1])
                            frozen_state = game.freeze_state(state)
                            
                            if (not game.terminal_test(state)) and state["ply"] <= 10:
                                game.to_research.append(frozen_state)
                
                            if frozen_state in used_states:
                                used_states[frozen_state] += 1
                                if used_states[frozen_state] >= 3:
                                    print "Draw by threefold repetition."
                                    game_over = True                             
                            else:
                                used_states[frozen_state] = 1
                        being_dragged = None
            
            # Key press logic
            elif event.type == KEYUP:
                # Restart key
                if event.key == K_r:
                    game_over = False
                    state = game.initial
                    previous_human_states = []
                    being_dragged = None
                    vacated_spot = None
                    last_moved_spot = None
                # Undo key
                if event.key == K_u and previous_human_states:
                    game_over = False
                    state = previous_human_states.pop()
                    being_dragged = None
                    vacated_spot = None
                    last_moved_spot = None
        
        if game.terminal_test(state) or game_over:
            
            game_over = True
            draw_everything()
            pygame.time.wait(3000)
            
            # Save best moves dictionary to pickled file
            symmetrize_saved_moves(game)
            game.dump_best_moves()
            print "best moves dictionary now has", len(game.best_moves), "entries."        
            print "unresearched states:", len(game.to_research)            
            
            if single_game:
                return None
                sys.exit()
                
            # New game
            print "\n\nNEW GAME\n"
            game_over = False
            state = game.initial
            previous_human_states = []
            used_states = {}
            being_dragged = None
            vacated_spot = None
            last_moved_spot = None
            if alternate:
                    humanity[-1], humanity[1], = humanity[1], humanity[-1]
                    ai[-1], ai[1], = ai[1], ai[-1]
        
        draw_everything()



################
### TRAINING ###
################

def train_to_depth(game,d,start=None):
    
    game.load_best_move()
    if not start:
        start = game.initial
  
    def try_all(state,depth):
        if depth > 0:
            i = len(game.actions(state))
            print "\nExploring", i, "moves of depth", d - depth, "\n"
            i = 0
            for action in t5.actions(state):
                i += 1
                print "move", i
                newstate = game.result(state,action)
                ab_player(game,newstate) # in the process, saves to best moves dictionary
                try_all(newstate,depth-1)
        return None
    
    print "best moves stored:", len(game.best_moves)
    try_all(start,d)
    print "best moves stored:", len(game.best_moves)
    
    game.dump_best_moves()
    
    
# Make saved best move dictionary symmetrical
    
def flip((r,c), ver=False, hor=False, size=5):
    row, col = r, c
    if ver:
        row = 2 * size - 2 - row
    if hor:
        col = 2 * size - 2 - col
    return (row, col)

def symmetrize_saved_moves(game):
    '''Creates eight way symmetry in the best moves dictionary of a game'''
    for frozenstate in game.best_moves.keys():
        mine,yours = frozenstate
        (bestmoves, val) = game.best_moves[frozenstate]
        for s1,s2 in [(0,1),(1,0),(1,1)]:
            mine2  = [flip(x,s1,s2,game.d) for x in mine]
            yours2 = [flip(x,s1,s2,game.d) for x in yours]
            moves2 = [tuple([flip(x,s1,s2,game.d) for x in move]) for move in bestmoves]
            game.best_moves[(frozenset(mine2),frozenset(yours2))] = (moves2, val)

def research_states(game, player=great_ab_player):
    '''Researches the best move for each position in a games to_research
    dictionary (after loading it) using the specified player.'''
    game.load_best_moves()
    num = len(game.to_research)
    i = 0
    while game.to_research:
        i += 1
        print "researching state", i, "of", num, "...\n"
        state = game.thaw_state(game.to_research.pop())
        state["pieces"][0] = state["pieces"][-1].union(state["pieces"][1])
        player(game,state)
    symmetrize_saved_moves(game)
    game.dump_best_moves()
    
    
###############
### RUN IT! ###
###############

t4 = Tessella(4)
t5 = Tessella(5)
t6 = Tessella(6)

#play_game(t5, query_player, dumb_ab_player)

#play_gui_game(t5, 1, 1)
#play_gui_game(t5, 1, 0, great_ab_player, alternate=True)
#play_gui_game(t5, 0, 0, great_ab_player, delay=500)
play_gui_game(t5, 0, 0, safe_great_ab_player, delay=500)
#play_gui_game(t5, 0, 0, great_ab_player, noisy_ab_player, alternate=True, lencap=8, delay=100)
#play_gui_game(t5, 0, 0, great_ab_player, faulty_ab_player, alternate=True, lencap=7, delay=100)
#play_gui_game(t5, 0, 0, great_ab_player, random_player, alternate=True, lencap=6)

#research_states(t5)

##################################play_gui_game(game, 0, 0, great_ab_player, faulty_ab_player, alternate=True, lencap=6, delay=100)
### SEE WHAT'S TAKING SO LONG ###
#################################

#rands = [t5.get_random_state(7,7) for i in range(50000)]

def test_code_efficiency():
    pr = cProfile.Profile()
    pr.enable()
    
    for r in rands:
        t5.step_moves(r)
        t5.capture_moves(r)
    #t5.best_moves = pickle.load( open( t5.savefile, "rb" ) )    
    #play_game(t5, great_ab_player, random_player)
    #ab_player(t5, t5.get_random_state(7,7))
    
    pr.disable()
    s = StringIO.StringIO()
    sortby = 'cumulative'
    ps = pstats.Stats(pr, stream=s).sort_stats(sortby)
    ps.print_stats()
    print s.getvalue()
