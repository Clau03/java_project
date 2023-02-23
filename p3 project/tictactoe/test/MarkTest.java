import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import tictactoe.src.Mark;

public class MarkTest {

    Mark mark;

    @Test
    public void MarkTest(){
        //Tests if the other() function returns the expected result:
            //if mark is XX, then OO is returned
            //if mark is OO, then XX is returned
            //if mark is EMPTY, then it stays empty
        mark = Mark.XX;
        Assertions.assertEquals(mark.other(), Mark.OO);
        mark = Mark.OO;
        Assertions.assertEquals(mark.other(), Mark.XX);
        mark = Mark.EMPTY;
        Assertions.assertEquals(mark.other(), Mark.EMPTY);
    }
}

