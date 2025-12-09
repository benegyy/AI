import random
from collections import defaultdict
from typing import Dict, List, Set, Tuple, Optional
import sys


class GridWorld:
    ACTIONS = [(0, 1), (1, 0), (0, -1), (-1, 0)]  # North, East, South, West
    ACTION_SYMBOLS = {0: '↑', 1: '→', 2: '↓', 3: '←'}

    def __init__(self, rows, cols, obstacles,pitfalls, goal,rewards):
        self.rows = rows
        self.cols = cols
        self.obstacles = obstacles
        self.pitfalls = pitfalls
        self.goal = goal
        self.rewards = rewards

    def is_valid_state(self, state):
        x, y = state
        return 1 <= x <= self.rows and 1 <= y <= self.cols and state not in self.obstacles

    def get_valid_states(self):
        return [(x, y) for x in range(1, self.rows + 1)
                for y in range(1, self.cols + 1)
                if self.is_valid_state((x, y))]

    def get_next_state(self, state, action):
        if self.is_terminal(state):
            return state

        dx, dy = self.ACTIONS[action]
        next_state = (state[0] + dx, state[1] + dy)

        return next_state if self.is_valid_state(next_state) else state

    def get_reward(self, state, next_state):
        if next_state == self.goal:
            return self.rewards['goal']
        elif next_state in self.pitfalls:
            return self.rewards['pitfall']
        elif next_state in self.obstacles:
            return self.rewards['obstacle']
        elif next_state == state:  # Hit wall or obstacle
            return self.rewards['default']
        return self.rewards['default']

    def is_terminal(self, state):
        return state == self.goal or state in self.pitfalls

    def manhattan_distance(self, state1,state2):
        return abs(state1[0] - state2[0]) + abs(state1[1] - state2[1])


def policy_iteration(grid_world, gamma, theta):

    def policy_evaluation(policy):
        V = defaultdict(float)
        V[grid_world.goal] = grid_world.rewards['goal']
        valid_states = grid_world.get_valid_states()

        for _ in range(100):
            delta = 0
            for state in valid_states:
                if state == grid_world.goal:
                    continue

                old_value = V[state]
                action = policy[state]
                next_state = grid_world.get_next_state(state, action)
                reward = grid_world.get_reward(state, next_state)

                V[state] = reward + gamma * V[next_state]
                delta = max(delta, abs(old_value - V[state]))

            if delta < theta:
                break

        return V

    def policy_improvement(V):
        policy = {}
        policy_stable = True
        valid_states = grid_world.get_valid_states()

        for state in valid_states:
            if state == grid_world.goal:
                continue

            old_action = policy.get(state, 0)
            max_value = float('-inf')
            best_action = old_action

            for action in range(4):
                next_state = grid_world.get_next_state(state, action)
                reward = grid_world.get_reward(state, next_state)
                value = reward + gamma * V[next_state]

                if value > max_value:
                    max_value = value
                    best_action = action

            policy[state] = best_action
            if old_action != best_action:
                policy_stable = False

        return policy, policy_stable

    policy = {state: 0 for state in grid_world.get_valid_states()
              if state != grid_world.goal}

    for _ in range(100):
        V = policy_evaluation(policy)
        new_policy, policy_stable = policy_improvement(V)

        if policy_stable:
            return new_policy
        policy = new_policy

    return policy


class SARSA:

    def __init__(self, env, alpha, gamma,
                 epsilon, visit_penalty: float = 0.01):
        self.env = env
        self.alpha = alpha
        self.gamma = gamma
        self.epsilon = epsilon
        self.visit_penalty = visit_penalty
        self.q_table = defaultdict(lambda: [0.0] * 4)
        self.visit_counts = defaultdict(int)
        self._initialize_q_values()

    def _initialize_q_values(self):
        for state in self.env.get_valid_states():
            if not self.env.is_terminal(state):
                dist = self.env.manhattan_distance(state, self.env.goal)
                init_value = max(0.1, 1.0 - (0.1 * dist))
                self.q_table[state] = [init_value] * 4

                for action in range(4):
                    next_state = self.env.get_next_state(state, action)
                    if next_state in self.env.obstacles:
                        self.q_table[state][action] = 0.1

        self.q_table[self.env.goal] = [self.env.rewards['goal']] * 4
        for pitfall in self.env.pitfalls:
            self.q_table[pitfall] = [self.env.rewards['pitfall']] * 4

    def get_valid_actions(self, state):
        if self.env.is_terminal(state):
            return []

        return [action for action in range(4)
                if self.env.get_next_state(state, action) != state
                or self.env.get_next_state(state, action) == self.env.goal]

    def choose_action(self, state, explore: bool = True):
        valid_actions = self.get_valid_actions(state)
        if not valid_actions:
            return 0

        if explore and random.random() < self.epsilon:
            return random.choice(valid_actions)

        max_q = max(self.q_table[state][a] for a in valid_actions)
        best_actions = [a for a in valid_actions
                        if self.q_table[state][a] == max_q]
        return random.choice(best_actions)

    def train(self, n_episodes):
        max_steps = self.env.rows * self.env.cols * 3

        for episode in range(n_episodes):
            state = self._get_random_start_state()
            action = self.choose_action(state)
            self.visit_counts[state] += 1

            for step in range(max_steps):
                next_state = self.env.get_next_state(state, action)
                if next_state in self.env.obstacles:
                    continue

                reward = self.env.get_reward(state, next_state)

                if self.env.is_terminal(next_state):
                    self._update_q_value(state, action, reward, next_state)
                    break

                next_action = self.choose_action(next_state)
                self._update_q_value(state, action, reward, next_state, next_action)

                state, action = next_state, next_action
                self.visit_counts[state] += 1

            self.epsilon = max(0.01, self.epsilon * 0.99)

        return self._create_policy_grid()

    def _get_random_start_state(self):
        while True:
            state = (random.randint(1, self.env.rows),
                     random.randint(1, self.env.cols))
            if not self.env.is_terminal(state) and state not in self.env.obstacles:
                return state

    def _update_q_value(self, state, action,reward, next_state,next_action: Optional[int] = None):
        if next_action is None:  # Terminal state
            self.q_table[state][action] = ((1 - self.alpha) *
                                           self.q_table[state][action] +
                                           self.alpha * (reward + self.gamma))
        else:
            distance_reward = 0.1 * (self.env.manhattan_distance(state, self.env.goal) -
                    self.env.manhattan_distance(next_state, self.env.goal))
            shaped_reward = reward + distance_reward

            self.q_table[state][action] += self.alpha * (
                    shaped_reward +
                    self.gamma * self.q_table[next_state][next_action] -
                    self.q_table[state][action] -
                    self.visit_penalty * self.visit_counts[(state, action)]
            )

    def _create_policy_grid(self):
        policy = [[None for _ in range(self.env.cols + 1)]
                  for _ in range(self.env.rows + 1)]

        for i in range(1, self.env.rows + 1):
            for j in range(1, self.env.cols + 1):
                state = (i, j)
                if state in self.env.obstacles:
                    policy[i][j] = 'O'
                elif state == self.env.goal:
                    policy[i][j] = 'G'
                elif state in self.env.pitfalls:
                    policy[i][j] = 'P'
                else:
                    valid_actions = self.get_valid_actions(state)
                    if valid_actions:
                        best_action = max(valid_actions,
                                          key=lambda a: self.q_table[state][a])
                        policy[i][j] = self.env.ACTION_SYMBOLS[best_action]

        return policy


def visualize_grid(rows, cols, grid_world,policy):
    print("\nOptimal Policy Grid:")
    for y in range(cols, 0, -1):
        for x in range(1, rows + 1):
            state = (x, y)
            if state in grid_world.obstacles:
                print("O", end=" ")
            elif state == grid_world.goal:
                print("G", end=" ")
            elif state in grid_world.pitfalls:
                print("P", end=" ")
            elif state in policy:
                print(grid_world.ACTION_SYMBOLS[policy[state]], end=" ")
            else:
                print(".", end=" ")
        print()


def main(input_file, output_file):
    with open(input_file, 'r') as f:
        lines = f.readlines()
    method = lines[0].strip()

    if method == 'P':  # Policy Iteration
        theta = float(lines[1].strip())
        gamma = float(lines[2].strip())
        rows, cols = map(int, lines[3].strip().split())
        idx = 4

    else:  # SARSA
        n_episodes = int(lines[1].strip())
        alpha = float(lines[2].strip())
        gamma = float(lines[3].strip())
        epsilon = float(lines[4].strip())
        rows, cols = map(int, lines[5].strip().split())
        idx = 6


    obstacles = set()
    num_obstacles = int(lines[idx].strip())
    idx += 1
    for _ in range(num_obstacles):
        x, y = map(int, lines[idx].strip().split())
        obstacles.add((x, y))
        idx += 1

    pitfalls = set()
    num_pitfalls = int(lines[idx].strip())
    idx += 1
    for _ in range(num_pitfalls):
        x, y = map(int, lines[idx].strip().split())
        pitfalls.add((x, y))
        idx += 1

    goal_x, goal_y = map(int, lines[idx].strip().split())
    goal = (goal_x, goal_y)
    idx += 1

    R_default, R_obstacle, R_pitfall, R_goal = map(float, lines[idx].strip().split())
    rewards = {
        'default': R_default,
        'obstacle': R_obstacle,
        'pitfall': R_pitfall,
        'goal': R_goal
    }

    env = GridWorld(rows, cols, obstacles, pitfalls, goal, rewards)
    with open(output_file, 'w') as f_out:

        if method == 'P':
            optimal_policy = policy_iteration(env, gamma, theta)
            states_to_print = sorted((x, y) for x in range(1, rows + 1)
                                     for y in range(1, cols + 1))
            for state, action in sorted(optimal_policy.items()):
                x, y = state
                #print(f"{x} {y} {optimal_policy.get(state, 0)}")
                f_out.write(f"{x} {y} {action}\n")

            visualize_grid(rows, cols, env, optimal_policy)
        else:  # SARSA
            agent = SARSA(env, alpha, gamma, epsilon)
            policy = agent.train(n_episodes)

            for i in range(1, rows + 1):
                for j in range(1, cols + 1):
                    state = (i, j)
                    if state == env.goal or state in env.obstacles or state in env.pitfalls:
                        # Print 0 for goal, obstacles, and pitfalls
                        f_out.write(f"{i} {j} 0\n")

                        #print(f"{i} {j} 0")
                    else:
                        valid_actions = agent.get_valid_actions(state)
                        if valid_actions:
                            best_action = max(valid_actions,
                                              key=lambda a: agent.q_table[state][a])
                            #print(f"{i} {j} {best_action}")
                            f_out.write(f"{i} {j} {best_action}\n")

                        else:
                            #print(f"{i} {j} 0")
                            f_out.write(f"{i} {j} 0\n")

            # Print policy grid
            for j in range(cols, 0, -1):
                print(" ".join(policy[i][j] or '.' for i in range(1, rows + 1)))


if __name__ == "__main__":
    if len(sys.argv) != 3:
        print("Usage: python3 e1234567_hw3.py input.txt output.txt")
        sys.exit(1)

    input_file = sys.argv[1]
    output_file = sys.argv[2]
    main(input_file, output_file)