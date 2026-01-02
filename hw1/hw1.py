from copy import deepcopy

def manhattan_distance(current_state, goal_state):
    distance = 0
    for i in range(4):
        for j in range(4):
            if current_state[i][j] != "_" and current_state[i][j] != goal_state[i][j]:
                goal_position = [(row, col) for row in range(4) for col in range(4) if goal_state[row][col] == current_state[i][j]][0]
                distance += abs(goal_position[0] - i) + abs(goal_position[1] - j)
    return distance

def generate_moves(current_state):
    moves = []
    # find the blank tile position
    blank_position = [(row, col) for row in range(4) for col in range(4) if current_state[row][col] == "_"][0]
    i, j = blank_position

    directions = [(-1, 0, 2), (1, 0, 2), (0, -1, 2), (0, 1, 2), (-2, 0, 3), (2, 0, 3), (0, -2, 3), (0, 2, 3)]

    for row_change,column_change , move_cost in directions:
        new_row = i + row_change
        new_col=  j + column_change

        if 0 <= new_row < 4 and 0 <= new_col < 4:
            new_state = deepcopy(current_state)
            new_state[i][j], new_state[new_row][new_col] = new_state[new_row][new_col], new_state[i][j]
            moves.append((new_state, move_cost))
    return moves

def a_star_search(initial_state, goal_state, max_cost):
    frontier = [(0, initial_state, [], 0)]  # (f, state, path, g)
    visited_states = set()

    while frontier:
        frontier.sort(key=lambda x: x[0]) #select lowest cost state
        f, current_state, path, g = frontier.pop(0)

        state_tuple = tuple(tuple(row) for row in current_state)

        if current_state == goal_state: #terminate
            print("SUCCESS")
            print()
            print_state(initial_state)
            for step in path:
                print_state(step)
            return "SUCCESS"

        if state_tuple in visited_states: #skip revisit
            continue

        visited_states.add(state_tuple) #if not mark

        for new_state, cost in generate_moves(current_state):
            new_path = path + [new_state]
            new_g = g + cost
            heuristic = manhattan_distance(new_state, goal_state)
            new_f = new_g + heuristic

            if new_f <= max_cost:
                frontier.append((new_f, new_state, new_path, new_g)) #add for exploration

    print("FAILURE")
    return "FAILURE"

def depth_first_iter(initial_state, goal_state, max_depth):
    def depth_limited_srch(state, path, depth, max_depth, visited):
        # Check if goal state is reached
        if state == goal_state:  #success
            print("SUCCESS")
            print()
            for step in path:
                print_state(step)
            return True
        if depth == max_depth:  #stop explore
            return False

        state_tuple = tuple(tuple(row) for row in state)  #convert to tuple to hash
        if state_tuple in visited:
            return False  # to avoid cycle
        visited.add(state_tuple)

        for new_state, _ in generate_moves(state):
            if depth_limited_srch(new_state, path + [new_state], depth + 1, max_depth, visited):
                return True
        visited.remove(state_tuple)
        return False

    #in each depth reset visited, call dls with new depth
    for depth in range(max_depth + 1):
        visited = set()
        if depth_limited_srch(initial_state, [initial_state], 0, depth, visited):
            return "SUCCESS"
    print("FAILURE")
    return "FAILURE"

def print_state(state):
    for row in state:
        print(" ".join(str(tile) for tile in row))
    print()

def main():
    #print("method (A* or DFIDS):")
    method = input().strip()
    #print("maximum cost or depth:")
    max_cost_depth = int(input().strip())
    #print("initial state:")
    initial_state = [input().strip().split() for _ in range(4)]
    #print("goal state:")
    goal_state = [input().strip().split() for _ in range(4)]

    if method == "A*":
        a_star_search(initial_state, goal_state, max_cost_depth)
    elif method == "DIFDS":
        depth_first_iter(initial_state, goal_state, max_cost_depth)

if __name__ == "__main__":
    main()
