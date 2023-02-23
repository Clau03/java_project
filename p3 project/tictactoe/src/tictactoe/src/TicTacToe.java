package tictactoe.src;

import utils.TextIO;

import java.util.HashMap;
import java.util.Map;

public class TicTacToe {
    protected static Map<String, Integer> scoreMap = new HashMap<>();

    public static void main(String[] args) throws InvalidIntegerNameException {

        String name1 = "";
        String name2 = "";

        int scorePlayer1 = 0, scorePlayer2 = 0;

        if (args.length < 2) {
            System.out.println("What is player 1's name? (will be X)");
            name1 = TextIO.getln();
            scoreMap.put(name1, scorePlayer1);

            System.out.println("What is player 2's name? (will be O)");
            name2 = TextIO.getln();
            scoreMap.put(name2, scorePlayer2);
        }

        if (args.length >= 2) {
            name1 = args[0];
            name2 = args[1];
        }

        try {
            if (name1.equals("") || name2.equals("")) {
                throw new InvalidEmptyNameException("InvalidEmptyNameException: Name cannot be empty.");
            }
            if (name1.matches(".*\\d+.*") || name2.matches(".*\\d+.*")) {
                throw new InvalidIntegerNameException("InvalidNameFormatException: Name cannot contain integers.");
            }
        } catch (InvalidEmptyNameException e ) {
            System.out.println(e.getMessage());
            System.out.println("What is player 1's name? (will be X)");
            name1 = TextIO.getln();
            scoreMap.put(name1, scorePlayer1);

            System.out.println("What is player 2's name? (will be O)");
            name2 = TextIO.getln();
            scoreMap.put(name2, scorePlayer2);
        } catch (InvalidIntegerNameException e) {
            System.out.println(e.getMessage());
            System.out.println("What is player 1's name? (will be X)");
            name1 = TextIO.getln();
            scoreMap.put(name1, scorePlayer1);

            System.out.println("What is player 2's name? (will be O)");
            name2 = TextIO.getln();
            scoreMap.put(name2, scorePlayer2);
        }

        Player player1;
        Player player2;

        switch (name1) {
            case "-N": {
                player1 = new ComputerPlayer(Mark.XX);
                break;
            }

            default: {
                player1 = new HumanPlayer(name1, Mark.XX);
                break;
            }
        }

        switch (name2) {
            case "-N": {
                player2 = new ComputerPlayer(Mark.OO);
                break;
            }

            default: {
                player2 = new HumanPlayer(name2, Mark.OO);
                break;
            }
        }

        Game game = new Game(player1, player2);
        game.start();
    }
}



