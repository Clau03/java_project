import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import tictactoe.src.*;

public class NaiveStrategyTest {

    Strategy naiveStrategy;
    ComputerPlayer naiveAI;
    Board board;

    @BeforeEach
    public void setup(){
        naiveStrategy = new NaiveStrategy();
        naiveAI = new ComputerPlayer(Mark.XX, naiveStrategy);
        board = new Board();
    }

    @Test
    public void getNameTest(){
        //Tests if the strategy is correctly identified
        Assertions.assertEquals("Naive Strategy", naiveStrategy.getName());
    }

    @Test
    public void  determineMoveTest(){
        //Tests if the naive strategy executes valid moves
        Assertions.assertTrue(naiveStrategy.determineMove(board,naiveAI.getMark())>=0 && naiveStrategy.determineMove(board,naiveAI.getMark())<=9);
    }
}
