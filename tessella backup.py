# -*- coding: utf-8 -*-
"""
Created on Mon Feb 02 19:49:28 2015

@author: Michael

This file contains game logic, game AI, and a graphical gameplay system
for the game Tessella. 

The graphical componenet uses pygames.py.

"""

from __future__ import division # Careful, this may cause problems
import os.path
import operator, copy, sys, pickle
import random
import pygame
from pygame.locals import *
from math import copysign

import timeit
import cProfile, pstats, StringIO, profile

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
        
        # Store which pairs of tiles are aligned
        self.aligned = {}
        for r in range(self.d*2-1):
            for c in range(self.d*2-1):
                for rr in range(self.d*2-1):
                    for cc in range(self.d*2-1):
                        if (r,c) != (rr,cc):
                            dr = rr - r
                            dc = cc - c
                            if abs(dc) == abs(dr) or dr * dc == 0:
                                self.aligned[((r,c),(rr,cc))] = cmp(dr,0), cmp(dc,0)

        # Create initial state
        friendly = set()
        enemy = set()
        for i in range(1,self.h-1):
            enemy.add((abs(self.d-i-1), i))
            friendly.add((self.h - 1 - abs(self.d-i-1), i))
        self.initial = {"player":1,"pieces":{1: friendly, -1: enemy},"ply":0}
        
        # Remember best moves of already seen board positions (speed up opengame), and killer moves per depth
        self.best_moves = {}
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
        
        # Make the move
        newstate["pieces"][player].remove((r,c))     # Pick up piece
        newstate["pieces"][-player].discard((rr,cc)) # Remove captured piece if any
        newstate["pieces"][player].add((rr,cc))      # Place at new location
        newstate["player"] = -player                 # Switch players
        newstate["ply"] += 1
        
        return newstate
        
    def step_moves(self,state):
        '''returns the set of states that are accessible from the current state via a step move'''
        moves = []
        player = state["player"]
        # Find all legal step moves
        for piece in state["pieces"][player]:
            for neighbor in self.neighbors[piece]:
                if not (neighbor in state["pieces"][1] or neighbor in state["pieces"][-1]):
                    moves.append((piece,neighbor))
        return moves
        
    def capture_moves(self,state): 
        '''returns the set of states that are accessible from the current state via a capture'''
        #BUG! captures pieces through own pieces...Problem with second while loop?
        moves = []
        player = state["player"]
        # Find all legal capture moves
        for piece in state["pieces"][player]:
            for backer in state["pieces"][player]:
                if not piece == backer:
                    if (backer,piece) in self.aligned:
                        direction = self.aligned[(backer,piece)]                       
                        selected = (backer[0]+direction[0], backer[1]+direction[1]) # tuple(sum(x) for x in zip(backer, direction))
                        cap_zone = False
                        while selected in self.tiles:
                            if selected == piece:
                                cap_zone = True
                            elif selected in state["pieces"][player]:
                                break
                            elif selected in state["pieces"][-player]:
                                if cap_zone:
                                    moves.append((piece,selected))
                                break
                            selected = (selected[0]+direction[0], selected[1]+direction[1]) # tuple(sum(x) for x in zip(selected, direction))
        return moves
    
    # Additional functions for the games.py module
    def actions(self, state):
        "Return a list of the allowable moves at this point."
        if self.terminal_test(state):
            return []
        else:
            return self.capture_moves(state) + self.step_moves(state)
    
    def spread(self, points):
        avgx = sum(x for (x,y) in points) * 1.0 / len(points)
        avgy = sum(y for (x,y) in points) * 1.0 / len(points)
        xerr = sum(abs(x - avgx) for (x,y) in points) / len(points)
        yerr = sum(abs(y - avgy) for (x,y) in points) / len(points)
        return xerr + yerr
    
    def periferality(self, points):
        return sum((abs(x - self.d + 1) + abs(y - self.d + 1)) for (x,y) in points) * 1.0 / len(points)
        
    def utility(self, state, player, n=0.0):
        '''Return the value to current player, which is made of five factors
        of decreasing importance: w
        1. whether the player has won,
        2. the piece count, 
        3. how clustered the players pieces are
        4. how central the pieces are,
        5. a random  noise factor
        '''
        
        noise = n
        mine, yours = state["pieces"][player], state["pieces"][-player]
        
        win_points = (len(yours) == self.d - 2) - (len(mine) == self.d - 2)      
        pieces_points = len(mine) - len(yours)
        clustered_points = self.spread(yours) - self.spread(mine)
        centrality_points = self.periferality(yours) - self.periferality(mine)
        
        return win_points * 1000 + pieces_points * 50 + clustered_points * 2 + centrality_points + random.random() * noise
    
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
    
    def get_random_state(self, whites, blacks):
        state = {}
        state["player"] = random.choice([-1,1])
        state["ply"] = 0
        state["pieces"] = {1:set(),-1:set()}
        
        lastrow = (self.d - 1) * 2
        w = b = 0
        while w < whites:
            r, c = random.randint(0,lastrow), random.randint(0,lastrow)
            if (r,c) in self.tiles and (r,c) not in state["pieces"][1]:
                state["pieces"][1].add((r,c))
                w += 1
        while b < blacks:
            r, c = random.randint(0,lastrow), random.randint(0,lastrow)
            if (r,c) in self.tiles and (r,c) not in state["pieces"][1] and (r,c) not in state["pieces"][-1]:
                state["pieces"][-1].add((r,c))
                b += 1
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
    if lookupbest and frozenstate in game.best_moves and noise == 0:
        move = random.choice(game.best_moves[frozenstate][0])
        print "looked up best move"
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
        
def ab_player(game, state, drawstates={}):
    print "ab player:"
    move = alphabeta_tessella_search(state, game, 3, 8, drawstates, storebest=True)
    print move, "\n"
    return move
    
def faulty_ab_player(game, state, drawstates={}):
    print "faulty ab player:"
    if random.random() > 0.6 or state["ply"] > 5:
        return ab_player(game, state, drawstates)
    else:
        print "oops!"
        return random_player(game, state)    
    
def fast_ab_player(game, state, drawstates={}):
    print "fast ab player:"
    move = alphabeta_tessella_search(state, game, 2, 8, drawstates)
    print move, "\n"
    return move
    
def crap_ab_player(game, state, drawstates={}):
    print "crap ab player:"
    move = alphabeta_tessella_search(state, game, 2, 8, drawstates, noise=1.0, lookupbest=False)
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

def play_gui_game(game, p1_humanity, p2_humanity, ai1=None, ai2=None, lencap=None, alternate=False):

    # Load best moves from pickled file
    if os.path.isfile(game.savefile):
        game.best_moves = pickle.load( open( game.savefile, "rb" ) )
    
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
            pygame.time.wait(750) # don't move instantly; wait 300 ms
            move = ai[state["player"]](game, state, used_states)
            state = game.result(state, move)
            vacated_spot = get_real_position(move[0])
            last_moved_spot = get_real_position(move[1])
            frozen_state = game.freeze_state(state) 
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
            pickle.dump( game.best_moves, open( game.savefile, "wb" ) )
            print "best moves dictionary now has", len(game.best_moves), "entries."
            
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

def train_to_depth(game,filename,d,start=None):
    
    game.best_moves = pickle.load( open( filename, "rb" ) )
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
                temp = ab_player(game,newstate) # in the process, saves to best moves dictionary of game object
                try_all(newstate,depth-1)
        return None
    
    print "best moves stored:", len(game.best_moves)
    try_all(start,d)
    print "best moves stored:", len(game.best_moves)
    
    pickle.dump( game.best_moves, open( filename, "wb" ) )
    
    
# Make saved best move dictionary symmetrical
    
def flip((r,c), ver=False, hor=False, size=5):
    row, col = r, c
    if ver:
        row = 2 * size - 2 - row
    if hor:
        col = 2 * size - 2 - col
    return (row, col)

def symmetrize_saved_moves(game):
    for frozenstate in game.best_moves.keys():
        mine,yours = frozenstate
        (bestmoves, val) = game.best_moves[frozenstate]
        for s1,s2 in [(0,1),(1,0),(1,1)]:
            mine2  = [flip(x,s1,s2,game.d) for x in mine]
            yours2 = [flip(x,s1,s2,game.d) for x in yours]
            moves2 = [tuple([flip(x,s1,s2,game.d) for x in move]) for move in bestmoves]
            game.best_moves[(frozenset(mine2),frozenset(yours2))] = (moves2, val)



###############
### RUN IT! ###
###############

t4 = Tessella(4)
t5 = Tessella(5)
t6 = Tessella(6)

game = t5

#play_game(game, query_player, dumb_ab_player)
#train_to_depth(game,"savedmoves.p",2)

#play_gui_game(game, 1, 0, ab_player, alternate=True)
play_gui_game(game, 0, 0, ab_player, faulty_ab_player, alternate=True)

def learn_some_states(game, toplay, tolearn, depth, startstate=None):
    game.best_moves = pickle.load( open( game.savefile, "rb" ) )
    common_states = {}
    
    for g in range(toplay):
        if g % 1000 == 0:
            print "game", g
        if startstate:
            state = startstate
        else:
            state = game.initial
        for d in range(depth):
            state = game.result(state,random_player(game,state,verbose=False))
        frozenstate = game.freeze_state(state)
        if frozenstate in common_states:
            common_states[frozenstate] += 1
        else:
            common_states[frozenstate] = 1
    
    cs = sorted(common_states.keys(), key = common_states.get)
    
    i = 0
    
    while cs and i < tolearn:
        fs = cs.pop()
        print "State appears in", common_states[fs], "games:\t", 
        if fs not in game.best_moves:
            ab_player(game,game.thaw_state(fs))
            symmetrize_saved_moves(game)
            pickle.dump( game.best_moves, open( game.savefile, "wb" ) )
            print "Game now has", len(game.best_moves), "moves stored.\n"
            i += 1
        else:
            print "already stored."
    
    return None


#learn_some_states(t5, 35000, 5, 7)
#play_gui_game(game, 0, 0, ab_player, random_player, alternate=True, lencap=7)


# SEE WHAT'S TAKING SO LONG
'''
pr = cProfile.Profile()
pr.enable()

ab_player(t5, t5.get_random_state(7,7))

pr.disable()
s = StringIO.StringIO()
sortby = 'cumulative'
ps = pstats.Stats(pr, stream=s).sort_stats(sortby)
ps.print_stats()
print s.getvalue()
'''