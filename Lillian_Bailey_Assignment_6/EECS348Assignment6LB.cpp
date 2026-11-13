
/* 
Description: Soduku Solver that reads puzzles from text files, solves them, and prints the solutions.
Inputs: Text files containing Sudoku puzzles
Outputs: Terminal messages
All Collaborators: Me, ChatGPT
Author: Joshua Assefa
Creation date: 10/13/2026
Revised by: Lillian Bailey
Revision date: 12NOV2026
*/

#include <array>      // Stores the Sudoku grid and bitmask tables.
#include <bitset>     // Counts the number of possible candidates for a cell.
#include <cctype>     // Provides character checking functions.
#include <cstddef>    // Provides std::size_t for solution counts.
#include <cstdint>    // Provides std::uint16_t for bitmasks.
#include <fstream>    // Reads puzzle files and writes solution files.
#include <functional> // Allows the search function to call a solution handler.
#include <iostream>   // Displays error messages.
#include <ostream>    // Provides output stream functionality.
#include <string>     // Stores filenames and messages.
#include <utility>    // Provides std::swap.
#include <vector>     // Stores the list of puzzle filenames.

// Keeps the Sudoku grid and solving functions together.
class SudokuSolver {
private:
    // --- Original code authored by Bruno Barron Silva ---

    static constexpr int SIZE = 9;
    static constexpr int BOX_SIZE = 3;
    static constexpr int CELLS = SIZE * SIZE;

    // Each bit represents whether a digit is already used.
    // Bits 1 through 9 represent the Sudoku digits.
    using Mask = std::uint16_t;
    static constexpr Mask ALL_DIGITS = 0x3FE;

    // The grid is stored in one array instead of a 2D array.
    // A value of 0 represents an empty cell.
    using Grid = std::array<int, CELLS>;

    // Called whenever the search finds a complete solution.
    using SolutionHandler =
        std::function<void(const Grid&, std::size_t)>;

    Grid grid{};

    // These masks track which digits are already used in each area.
    std::array<Mask, SIZE> rowUsed{};
    std::array<Mask, SIZE> colUsed{};
    std::array<Mask, SIZE> boxUsed{};

    // Stores the positions of cells that need to be filled.
    std::array<int, CELLS> empties{};
    int emptyCount = 0;

    // Tracks the number of complete solutions found.
    std::size_t solutionCount = 0;

    // Converts a row and column into the corresponding 3x3 box number.
    int boxOf(int row, int col) const {
        return (row / BOX_SIZE) * BOX_SIZE + (col / BOX_SIZE);
    }

    // Finds all digits that can legally be placed in a particular cell.
    Mask candidatesFor(int cell) const {
        int row = cell / SIZE;
        int col = cell % SIZE;

        // Combine the digits already used in the cell's row, column, and box.
        Mask used =
            rowUsed[row] |
            colUsed[col] |
            boxUsed[boxOf(row, col)];

        // Return the digits that are not already used.
        return static_cast<Mask>(ALL_DIGITS & ~used);
    }

    // Records the starting digits and checks whether any given clues conflict.
    bool prepareSearch() {
        // Clear the masks before processing a new puzzle.
        rowUsed.fill(0);
        colUsed.fill(0);
        boxUsed.fill(0);

        emptyCount = 0;

        // Examine every cell in the puzzle.
        for (int cell = 0; cell < CELLS; ++cell) {
            int value = grid[cell];

            if (value == 0) {
                // Remember blank cells so the search can fill them later.
                empties[emptyCount++] = cell;
                continue;
            }

            int row = cell / SIZE;
            int col = cell % SIZE;
            int box = boxOf(row, col);

            // Create the bit corresponding to the given digit.
            Mask bit = static_cast<Mask>(1u << value);

            // A repeated digit means the starting puzzle is invalid.
            if ((rowUsed[row] | colUsed[col] | boxUsed[box]) & bit) {
                return false;
            }

            // Record the given digit in its row, column, and box.
            rowUsed[row] |= bit;
            colUsed[col] |= bit;
            boxUsed[box] |= bit;
        }

        return true;
    }

    // Uses recursive backtracking to find every valid solution.
    void search(int depth, const SolutionHandler& onSolution) {
        // A solution is complete when every empty cell has been filled.
        if (depth == emptyCount) {
            ++solutionCount;
            onSolution(grid, solutionCount);
            return;
        }

        // Find the remaining empty cell with the fewest legal candidates.
        // This is the minimum-remaining-values (MRV) strategy.
        int bestIndex = depth;
        int bestCount = SIZE + 1;
        Mask bestMask = 0;

        for (int i = depth; i < emptyCount; ++i) {
            Mask mask = candidatesFor(empties[i]);
            int count = static_cast<int>(std::bitset<16>(mask).count());

            // A cell with no legal candidates means this branch cannot work.
            if (count == 0) {
                return;
            }

            if (count < bestCount) {
                bestCount = count;
                bestIndex = i;
                bestMask = mask;

                // A cell with one candidate cannot be improved upon.
                if (count == 1) {
                    break;
                }
            }
        }

        // Move the most-constrained cell to the current search position.
        std::swap(empties[depth], empties[bestIndex]);

        int cell = empties[depth];
        int row = cell / SIZE;
        int col = cell % SIZE;
        int box = boxOf(row, col);

        // Try each legal digit in the selected cell.
        for (int digit = 1; digit <= SIZE; ++digit) {
            Mask bit = static_cast<Mask>(1u << digit);

            // Skip digits that are not valid candidates.
            if (!(bestMask & bit)) {
                continue;
            }

            // Temporarily place the digit and update the corresponding masks.
            grid[cell] = digit;
            rowUsed[row] |= bit;
            colUsed[col] |= bit;
            boxUsed[box] |= bit;

            // Continue filling the remaining empty cells.
            search(depth + 1, onSolution);

            // Undo the temporary placement before trying another candidate.
            grid[cell] = 0;
            rowUsed[row] ^= bit;
            colUsed[col] ^= bit;
            boxUsed[box] ^= bit;
        }
    }

    // --- Revised code by Joshua Assefa ---

    // Writes a completed grid as nine rows of nine space-separated digits.
    void writeGrid(const Grid& board, std::ostream& outFile) const {
        for (int row = 0; row < SIZE; ++row) {
            for (int col = 0; col < SIZE; ++col) {
                if (col > 0) {
                    outFile << " ";
                }

                outFile << board[row * SIZE + col];
            }

            outFile << "\n";
        }
    }

    // Extracts the puzzle number from a filename, ignoring directory names.
    int extractPuzzleNumber(const std::string& filename) const {
        std::string numStr = "";

        std::size_t slash = filename.find_last_of("/\\");
        std::size_t start =
            (slash == std::string::npos) ? 0 : slash + 1;

        for (std::size_t i = start; i < filename.size(); ++i) {
            if (std::isdigit(
                static_cast<unsigned char>(filename[i]))) {
                numStr += filename[i];
            }
        }

        return numStr.empty() ? 1 : std::stoi(numStr);
    }

public:
    // --- Original file loading logic authored by Bruno Barron Silva ---

    // Reads a puzzle file and verifies that it contains exactly 81 valid cells.
    bool loadFromFile(const std::string& filename) {
        std::ifstream inputFile(filename);

        if (!inputFile) {
            std::cerr << "Error: could not open "
                      << filename << ".\n";
            return false;
        }

        // Use a temporary grid so an invalid file cannot partially overwrite
        // the current puzzle.
        Grid loaded{};
        int cellCount = 0;
        char character;

        while (inputFile.get(character)) {
            // Ignore spaces, tabs, and newline characters.
            if (std::isspace(
                static_cast<unsigned char>(character))) {
                continue;
            }

            // Reject any non-whitespace character beyond the 81st cell.
            if (cellCount == CELLS) {
                std::cerr << "Error: " << filename
                          << " contains more than 81 cells.\n";
                return false;
            }

            int value = 0;

            if (character == '_') {
                // An underscore represents an empty cell.
                value = 0;
            }
            else if (character >= '1' && character <= '9') {
                // Convert a valid digit character into an integer.
                value = character - '0';
            }
            else {
                std::cerr << "Error: invalid character '"
                          << character << "' in "
                          << filename << "\n";
                return false;
            }

            loaded[cellCount++] = value;
        }

        // The puzzle must contain exactly 81 cell characters.
        if (cellCount != CELLS) {
            std::cerr << "Error: " << filename
                      << " must contain exactly 81 cells.\n";
            return false;
        }

        // Only replace the current grid after the file passes validation.
        grid = loaded;

        return true;
    }

    // --- Revised solve and write logic by Joshua Assefa ---

    // Runs the search and writes every solution to the shared output file.
    void solveAndWrite(std::ostream& outFile) {
        // Reset the solution count before processing this puzzle.
        solutionCount = 0;

        // Check whether the starting puzzle contains conflicting clues.
        if (!prepareSearch()) {
            outFile << "No solution found.\n";
            return;
        }

        // This function is called each time the search finds a solution.
        auto writeSolution = [this, &outFile](
            const Grid& solved, std::size_t) {
            writeGrid(solved, outFile);
        };

        // Start the recursive search with the first empty cell.
        search(0, writeSolution);

        // Record whether the search found any complete solutions.
        if (solutionCount == 0) {
            outFile << "No solution found.\n";
        }
        else {
            outFile << "Solutions found: "
                    << solutionCount << "\n";
        }
    }
};

// --- Original main by Bruno Barron Silva,
//     output routing modified by Joshua Assefa ---

int main(int argc, char* argv[]) {
    std::vector<std::string> filenames;

    // Collect puzzle filenames supplied through command-line arguments.
    for (int i = 1; i < argc; ++i) {
        filenames.push_back(argv[i]);
    }

    // Use the five required puzzle files if no arguments were supplied.
    if (filenames.empty()) {
        filenames = {
            "puzzle1.txt",
            "puzzle2.txt",
            "puzzle3.txt",
            "puzzle4.txt",
            "puzzle5.txt"
        };
    }

    // Store the results for all puzzles in one output file.
    std::ofstream outFile("solutions.txt");

    if (!outFile) {
        std::cerr << "Error: could not create solutions.txt\n";
        return 1;
    }

    SudokuSolver solver;
    bool allLoaded = true;

    // Process each puzzle separately while keeping the results in one file.
    for (const std::string& filename : filenames) {
        // Remove the directory path so the header shows only the filename.
        std::size_t slash = filename.find_last_of("/\\");

        std::string puzzleName =
            (slash == std::string::npos)
            ? filename
            : filename.substr(slash + 1);

        // Start a new puzzle section in the output file.
        outFile << "Puzzle: " << puzzleName << "\n";

        if (solver.loadFromFile(filename)) {
            // Solve the puzzle and write its solutions and solution count.
            solver.solveAndWrite(outFile);
        }
        else {
            // Record the required message when a puzzle cannot be loaded.
            outFile << "No solution found.\n";
            allLoaded = false;
        }

        // Leave a blank line between puzzle sections.
        outFile << "\n";
    }

    // Check for errors that occurred while writing the output file.
    if (!outFile) {
        std::cerr << "Error: writing to solutions.txt failed.\n";
        return 1;
    }

    return allLoaded ? 0 : 1;
}
