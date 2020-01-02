
//----------------------------------------------------
// The following code was generated by CUP v0.11a beta 20060608
// Thu Jan 02 19:42:24 CET 2020
//----------------------------------------------------

package grammar;


/** CUP v0.11a beta 20060608 generated parser.
  * @version Thu Jan 02 19:42:24 CET 2020
  */
public class parser extends java_cup.runtime.lr_parser {

  /** Default constructor. */
  public parser() {super();}

  /** Constructor which sets the default scanner. */
  public parser(java_cup.runtime.Scanner s) {super(s);}

  /** Constructor which sets the default scanner. */
  public parser(java_cup.runtime.Scanner s, java_cup.runtime.SymbolFactory sf) {super(s,sf);}

  /** Production table. */
  protected static final short _production_table[][] = 
    unpackFromStrings(new String[] {
    "\000\053\000\002\002\004\000\002\002\016\000\002\003" +
    "\007\000\002\004\006\000\002\005\010\000\002\005\005" +
    "\000\002\005\005\000\002\006\006\000\002\007\007\000" +
    "\002\010\006\000\002\011\006\000\002\011\005\000\002" +
    "\012\006\000\002\013\007\000\002\013\007\000\002\013" +
    "\007\000\002\013\005\000\002\013\005\000\002\013\003" +
    "\000\002\013\003\000\002\013\003\000\002\013\005\000" +
    "\002\013\005\000\002\014\002\000\002\014\005\000\002" +
    "\015\003\000\002\015\006\000\002\016\002\000\002\016" +
    "\003\000\002\016\005\000\002\017\004\000\002\017\002" +
    "\000\002\020\003\000\002\020\003\000\002\021\002\000" +
    "\002\021\003\000\002\021\005\000\002\022\002\000\002" +
    "\022\003\000\002\022\005\000\002\023\002\000\002\023" +
    "\003\000\002\023\005" });

  /** Access to production table. */
  public short[][] production_table() {return _production_table;}

  /** Parse-action table. */
  protected static final short[][] _action_table = 
    unpackFromStrings(new String[] {
    "\000\153\000\004\015\005\001\002\000\004\002\155\001" +
    "\002\000\004\004\007\001\002\000\006\020\uffe2\023\040" +
    "\001\002\000\004\025\010\001\002\000\004\006\035\001" +
    "\002\000\010\021\uffdc\041\016\042\014\001\002\000\004" +
    "\010\032\001\002\000\006\007\030\021\uffdb\001\002\000" +
    "\022\005\uffe1\007\uffe1\010\uffe1\011\uffe1\013\uffe1\021\uffe1" +
    "\041\uffe1\042\uffe1\001\002\000\004\021\017\001\002\000" +
    "\022\005\uffe0\007\uffe0\010\uffe0\011\uffe0\013\uffe0\021\uffe0" +
    "\041\uffe0\042\uffe0\001\002\000\004\006\022\001\002\000" +
    "\004\005\021\001\002\000\040\002\ufff9\016\ufff9\017\ufff9" +
    "\020\ufff9\022\ufff9\023\ufff9\024\ufff9\026\ufff9\027\ufff9\031" +
    "\ufff9\032\ufff9\033\ufff9\036\ufff9\037\ufff9\040\ufff9\001\002" +
    "\000\010\007\uffd9\041\016\042\014\001\002\000\012\005" +
    "\uffd8\007\uffd8\013\026\021\uffd8\001\002\000\004\007\025" +
    "\001\002\000\004\005\ufff5\001\002\000\014\005\uffd9\007" +
    "\uffd9\021\uffd9\041\016\042\014\001\002\000\010\005\uffd7" +
    "\007\uffd7\021\uffd7\001\002\000\010\021\uffdc\041\016\042" +
    "\014\001\002\000\004\021\uffda\001\002\000\006\041\016" +
    "\042\014\001\002\000\012\007\ufff6\021\ufff6\041\016\042" +
    "\014\001\002\000\006\007\ufff7\021\ufff7\001\002\000\006" +
    "\041\016\042\014\001\002\000\004\007\037\001\002\000" +
    "\010\021\ufff8\041\ufff8\042\ufff8\001\002\000\004\007\154" +
    "\001\002\000\004\020\042\001\002\000\004\004\044\001" +
    "\002\000\004\014\075\001\002\000\004\025\046\001\002" +
    "\000\012\021\uffdf\030\053\041\016\042\014\001\002\000" +
    "\004\006\047\001\002\000\006\041\016\042\014\001\002" +
    "\000\004\007\051\001\002\000\012\021\ufffe\030\ufffe\041" +
    "\ufffe\042\ufffe\001\002\000\004\010\070\001\002\000\004" +
    "\006\066\001\002\000\006\007\064\021\uffde\001\002\000" +
    "\004\021\057\001\002\000\004\005\063\001\002\000\004" +
    "\006\060\001\002\000\010\007\uffd9\041\016\042\014\001" +
    "\002\000\004\007\062\001\002\000\004\005\ufffa\001\002" +
    "\000\004\014\uffff\001\002\000\012\021\uffdf\030\053\041" +
    "\016\042\014\001\002\000\004\021\uffdd\001\002\000\012" +
    "\007\uffd9\021\uffd9\041\016\042\014\001\002\000\006\007" +
    "\ufffb\021\ufffb\001\002\000\006\041\016\042\014\001\002" +
    "\000\012\007\ufffc\021\ufffc\041\016\042\014\001\002\000" +
    "\004\011\073\001\002\000\006\041\016\042\014\001\002" +
    "\000\006\007\ufffd\021\ufffd\001\002\000\004\004\007\001" +
    "\002\000\004\016\077\001\002\000\004\004\007\001\002" +
    "\000\004\017\101\001\002\000\004\004\007\001\002\000" +
    "\030\002\uffea\022\uffea\024\uffea\026\uffea\027\uffea\031\uffea" +
    "\032\uffea\033\uffea\036\uffea\037\uffea\040\uffea\001\002\000" +
    "\030\002\000\022\115\024\114\026\113\027\111\031\112" +
    "\032\110\033\107\036\106\037\105\040\104\001\002\000" +
    "\004\007\uffef\001\002\000\004\006\150\001\002\000\004" +
    "\006\136\001\002\000\004\006\134\001\002\000\004\007" +
    "\uffed\001\002\000\004\006\132\001\002\000\004\007\uffee" +
    "\001\002\000\004\006\126\001\002\000\004\006\124\001" +
    "\002\000\004\006\120\001\002\000\004\007\117\001\002" +
    "\000\030\002\uffe9\022\uffe9\024\uffe9\026\uffe9\027\uffe9\031" +
    "\uffe9\032\uffe9\033\uffe9\036\uffe9\037\uffe9\040\uffe9\001\002" +
    "\000\004\042\121\001\002\000\004\012\122\001\002\000" +
    "\004\042\123\001\002\000\004\007\ufff3\001\002\000\004" +
    "\042\125\001\002\000\004\007\ufff0\001\002\000\004\042" +
    "\127\001\002\000\004\012\130\001\002\000\004\042\131" +
    "\001\002\000\004\007\ufff2\001\002\000\004\042\133\001" +
    "\002\000\004\007\uffec\001\002\000\004\042\135\001\002" +
    "\000\004\007\uffeb\001\002\000\010\007\uffe6\034\142\035" +
    "\141\001\002\000\006\007\uffe5\013\146\001\002\000\004" +
    "\007\ufff1\001\002\000\004\004\143\001\002\000\006\007" +
    "\uffe8\013\uffe8\001\002\000\010\005\uffd9\041\016\042\014" +
    "\001\002\000\004\005\145\001\002\000\006\007\uffe7\013" +
    "\uffe7\001\002\000\010\007\uffe6\034\142\035\141\001\002" +
    "\000\004\007\uffe4\001\002\000\004\042\151\001\002\000" +
    "\004\012\152\001\002\000\004\042\153\001\002\000\004" +
    "\007\ufff4\001\002\000\004\020\uffe3\001\002\000\004\002" +
    "\001\001\002" });

  /** Access to parse-action table. */
  public short[][] action_table() {return _action_table;}

  /** <code>reduce_goto</code> table. */
  protected static final short[][] _reduce_table = 
    unpackFromStrings(new String[] {
    "\000\153\000\004\002\003\001\001\000\002\001\001\000" +
    "\004\007\005\001\001\000\004\017\040\001\001\000\004" +
    "\010\010\001\001\000\002\001\001\000\010\011\012\020" +
    "\011\022\014\001\001\000\002\001\001\000\002\001\001" +
    "\000\002\001\001\000\004\012\017\001\001\000\002\001" +
    "\001\000\002\001\001\000\002\001\001\000\002\001\001" +
    "\000\006\020\022\023\023\001\001\000\002\001\001\000" +
    "\002\001\001\000\002\001\001\000\006\020\022\023\026" +
    "\001\001\000\002\001\001\000\010\011\012\020\011\022" +
    "\030\001\001\000\002\001\001\000\004\020\032\001\001" +
    "\000\004\020\033\001\001\000\002\001\001\000\004\020" +
    "\035\001\001\000\002\001\001\000\002\001\001\000\002" +
    "\001\001\000\002\001\001\000\004\003\042\001\001\000" +
    "\002\001\001\000\004\004\044\001\001\000\010\005\053" +
    "\020\051\021\054\001\001\000\002\001\001\000\004\020" +
    "\047\001\001\000\002\001\001\000\002\001\001\000\002" +
    "\001\001\000\002\001\001\000\002\001\001\000\004\006" +
    "\055\001\001\000\002\001\001\000\002\001\001\000\006" +
    "\020\022\023\060\001\001\000\002\001\001\000\002\001" +
    "\001\000\002\001\001\000\010\005\053\020\051\021\064" +
    "\001\001\000\002\001\001\000\006\020\022\023\066\001" +
    "\001\000\002\001\001\000\004\020\070\001\001\000\004" +
    "\020\071\001\001\000\002\001\001\000\004\020\073\001" +
    "\001\000\002\001\001\000\004\007\075\001\001\000\002" +
    "\001\001\000\004\007\077\001\001\000\002\001\001\000" +
    "\004\007\101\001\001\000\004\014\102\001\001\000\004" +
    "\013\115\001\001\000\002\001\001\000\002\001\001\000" +
    "\002\001\001\000\002\001\001\000\002\001\001\000\002" +
    "\001\001\000\002\001\001\000\002\001\001\000\002\001" +
    "\001\000\002\001\001\000\002\001\001\000\002\001\001" +
    "\000\002\001\001\000\002\001\001\000\002\001\001\000" +
    "\002\001\001\000\002\001\001\000\002\001\001\000\002" +
    "\001\001\000\002\001\001\000\002\001\001\000\002\001" +
    "\001\000\002\001\001\000\002\001\001\000\002\001\001" +
    "\000\002\001\001\000\006\015\136\016\137\001\001\000" +
    "\002\001\001\000\002\001\001\000\002\001\001\000\002" +
    "\001\001\000\006\020\022\023\143\001\001\000\002\001" +
    "\001\000\002\001\001\000\006\015\136\016\146\001\001" +
    "\000\002\001\001\000\002\001\001\000\002\001\001\000" +
    "\002\001\001\000\002\001\001\000\002\001\001\000\002" +
    "\001\001" });

  /** Access to <code>reduce_goto</code> table. */
  public short[][] reduce_table() {return _reduce_table;}

  /** Instance of action encapsulation class. */
  protected CUP$parser$actions action_obj;

  /** Action encapsulation object initializer. */
  protected void init_actions()
    {
      action_obj = new CUP$parser$actions(this);
    }

  /** Invoke a user supplied parse action. */
  public java_cup.runtime.Symbol do_action(
    int                        act_num,
    java_cup.runtime.lr_parser parser,
    java.util.Stack            stack,
    int                        top)
    throws java.lang.Exception
  {
    /* call code in generated class */
    return action_obj.CUP$parser$do_action(act_num, parser, stack, top);
  }

  /** Indicates start state. */
  public int start_state() {return 0;}
  /** Indicates start production. */
  public int start_production() {return 0;}

  /** <code>EOF</code> Symbol index. */
  public int EOF_sym() {return 0;}

  /** <code>error</code> Symbol index. */
  public int error_sym() {return 1;}



  public grammar.Absyn.ModelRule pModelRule() throws Exception
  {
	java_cup.runtime.Symbol res = parse();
	return (grammar.Absyn.ModelRule) res.value;
  }

public <B,A extends java.util.LinkedList<? super B>> A cons_(B x, A xs) { xs.addFirst(x); return xs; }

public void syntax_error(java_cup.runtime.Symbol cur_token)
{
	report_error("Syntax Error, trying to recover and continue parse...", cur_token);
}

public void unrecovered_syntax_error(java_cup.runtime.Symbol cur_token) throws java.lang.Exception
{
	throw new Exception("Unrecoverable Syntax Error");
}


}

/** Cup generated class to encapsulate user supplied action code.*/
class CUP$parser$actions {
  private final parser parser;

  /** Constructor */
  CUP$parser$actions(parser parser) {
    this.parser = parser;
  }

  /** Method with the actual generated action code. */
  public final java_cup.runtime.Symbol CUP$parser$do_action(
    int                        CUP$parser$act_num,
    java_cup.runtime.lr_parser CUP$parser$parser,
    java.util.Stack            CUP$parser$stack,
    int                        CUP$parser$top)
    throws java.lang.Exception
    {
      /* Symbol object for return from actions */
      java_cup.runtime.Symbol CUP$parser$result;

      /* select the action based on the action number */
      switch (CUP$parser$act_num)
        {
          /*. . . . . . . . . . . . . . . . . . . .*/
          case 42: // ListName ::= Name _SYMB_7 ListName 
            {
              grammar.Absyn.ListName RESULT =null;
		grammar.Absyn.Name p_1 = (grammar.Absyn.Name)((java_cup.runtime.Symbol) CUP$parser$stack.elementAt(CUP$parser$top-2)).value;
		grammar.Absyn.ListName p_3 = (grammar.Absyn.ListName)((java_cup.runtime.Symbol) CUP$parser$stack.peek()).value;
		 RESULT = p_3; p_3.addFirst(p_1); 
              CUP$parser$result = parser.getSymbolFactory().newSymbol("ListName",17, RESULT);
            }
          return CUP$parser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 41: // ListName ::= Name 
            {
              grammar.Absyn.ListName RESULT =null;
		grammar.Absyn.Name p_1 = (grammar.Absyn.Name)((java_cup.runtime.Symbol) CUP$parser$stack.peek()).value;
		 RESULT = new grammar.Absyn.ListName(); RESULT.addLast(p_1); 
              CUP$parser$result = parser.getSymbolFactory().newSymbol("ListName",17, RESULT);
            }
          return CUP$parser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 40: // ListName ::= 
            {
              grammar.Absyn.ListName RESULT =null;
		 RESULT = new grammar.Absyn.ListName(); 
              CUP$parser$result = parser.getSymbolFactory().newSymbol("ListName",17, RESULT);
            }
          return CUP$parser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 39: // ListAutomataTransitionRule ::= AutomataTransitionRule _SYMB_3 ListAutomataTransitionRule 
            {
              grammar.Absyn.ListAutomataTransitionRule RESULT =null;
		grammar.Absyn.AutomataTransitionRule p_1 = (grammar.Absyn.AutomataTransitionRule)((java_cup.runtime.Symbol) CUP$parser$stack.elementAt(CUP$parser$top-2)).value;
		grammar.Absyn.ListAutomataTransitionRule p_3 = (grammar.Absyn.ListAutomataTransitionRule)((java_cup.runtime.Symbol) CUP$parser$stack.peek()).value;
		 RESULT = p_3; p_3.addFirst(p_1); 
              CUP$parser$result = parser.getSymbolFactory().newSymbol("ListAutomataTransitionRule",16, RESULT);
            }
          return CUP$parser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 38: // ListAutomataTransitionRule ::= AutomataTransitionRule 
            {
              grammar.Absyn.ListAutomataTransitionRule RESULT =null;
		grammar.Absyn.AutomataTransitionRule p_1 = (grammar.Absyn.AutomataTransitionRule)((java_cup.runtime.Symbol) CUP$parser$stack.peek()).value;
		 RESULT = new grammar.Absyn.ListAutomataTransitionRule(); RESULT.addLast(p_1); 
              CUP$parser$result = parser.getSymbolFactory().newSymbol("ListAutomataTransitionRule",16, RESULT);
            }
          return CUP$parser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 37: // ListAutomataTransitionRule ::= 
            {
              grammar.Absyn.ListAutomataTransitionRule RESULT =null;
		 RESULT = new grammar.Absyn.ListAutomataTransitionRule(); 
              CUP$parser$result = parser.getSymbolFactory().newSymbol("ListAutomataTransitionRule",16, RESULT);
            }
          return CUP$parser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 36: // ListTransitionRule ::= TransitionRule _SYMB_3 ListTransitionRule 
            {
              grammar.Absyn.ListTransitionRule RESULT =null;
		grammar.Absyn.TransitionRule p_1 = (grammar.Absyn.TransitionRule)((java_cup.runtime.Symbol) CUP$parser$stack.elementAt(CUP$parser$top-2)).value;
		grammar.Absyn.ListTransitionRule p_3 = (grammar.Absyn.ListTransitionRule)((java_cup.runtime.Symbol) CUP$parser$stack.peek()).value;
		 RESULT = p_3; p_3.addFirst(p_1); 
              CUP$parser$result = parser.getSymbolFactory().newSymbol("ListTransitionRule",15, RESULT);
            }
          return CUP$parser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 35: // ListTransitionRule ::= TransitionRule 
            {
              grammar.Absyn.ListTransitionRule RESULT =null;
		grammar.Absyn.TransitionRule p_1 = (grammar.Absyn.TransitionRule)((java_cup.runtime.Symbol) CUP$parser$stack.peek()).value;
		 RESULT = new grammar.Absyn.ListTransitionRule(); RESULT.addLast(p_1); 
              CUP$parser$result = parser.getSymbolFactory().newSymbol("ListTransitionRule",15, RESULT);
            }
          return CUP$parser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 34: // ListTransitionRule ::= 
            {
              grammar.Absyn.ListTransitionRule RESULT =null;
		 RESULT = new grammar.Absyn.ListTransitionRule(); 
              CUP$parser$result = parser.getSymbolFactory().newSymbol("ListTransitionRule",15, RESULT);
            }
          return CUP$parser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 33: // Name ::= LabelIdent 
            {
              grammar.Absyn.Name RESULT =null;
		String p_1 = (String)((java_cup.runtime.Symbol) CUP$parser$stack.peek()).value;
		 RESULT = new grammar.Absyn.LiteralName(p_1); 
              CUP$parser$result = parser.getSymbolFactory().newSymbol("Name",14, RESULT);
            }
          return CUP$parser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 32: // Name ::= MyInteger 
            {
              grammar.Absyn.Name RESULT =null;
		String p_1 = (String)((java_cup.runtime.Symbol) CUP$parser$stack.peek()).value;
		 RESULT = new grammar.Absyn.NumberName(p_1); 
              CUP$parser$result = parser.getSymbolFactory().newSymbol("Name",14, RESULT);
            }
          return CUP$parser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 31: // MaybeClosed ::= 
            {
              grammar.Absyn.MaybeClosed RESULT =null;
		 RESULT = new grammar.Absyn.NotClosedInit(); 
              CUP$parser$result = parser.getSymbolFactory().newSymbol("MaybeClosed",13, RESULT);
            }
          return CUP$parser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 30: // MaybeClosed ::= _SYMB_15 _SYMB_3 
            {
              grammar.Absyn.MaybeClosed RESULT =null;
		 RESULT = new grammar.Absyn.ClosedInit(); 
              CUP$parser$result = parser.getSymbolFactory().newSymbol("MaybeClosed",13, RESULT);
            }
          return CUP$parser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 29: // ListSymmetryOption ::= SymmetryOption _SYMB_7 ListSymmetryOption 
            {
              grammar.Absyn.ListSymmetryOption RESULT =null;
		grammar.Absyn.SymmetryOption p_1 = (grammar.Absyn.SymmetryOption)((java_cup.runtime.Symbol) CUP$parser$stack.elementAt(CUP$parser$top-2)).value;
		grammar.Absyn.ListSymmetryOption p_3 = (grammar.Absyn.ListSymmetryOption)((java_cup.runtime.Symbol) CUP$parser$stack.peek()).value;
		 RESULT = p_3; p_3.addFirst(p_1); 
              CUP$parser$result = parser.getSymbolFactory().newSymbol("ListSymmetryOption",12, RESULT);
            }
          return CUP$parser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 28: // ListSymmetryOption ::= SymmetryOption 
            {
              grammar.Absyn.ListSymmetryOption RESULT =null;
		grammar.Absyn.SymmetryOption p_1 = (grammar.Absyn.SymmetryOption)((java_cup.runtime.Symbol) CUP$parser$stack.peek()).value;
		 RESULT = new grammar.Absyn.ListSymmetryOption(); RESULT.addLast(p_1); 
              CUP$parser$result = parser.getSymbolFactory().newSymbol("ListSymmetryOption",12, RESULT);
            }
          return CUP$parser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 27: // ListSymmetryOption ::= 
            {
              grammar.Absyn.ListSymmetryOption RESULT =null;
		 RESULT = new grammar.Absyn.ListSymmetryOption(); 
              CUP$parser$result = parser.getSymbolFactory().newSymbol("ListSymmetryOption",12, RESULT);
            }
          return CUP$parser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 26: // SymmetryOption ::= _SYMB_25 _SYMB_0 ListName _SYMB_1 
            {
              grammar.Absyn.SymmetryOption RESULT =null;
		grammar.Absyn.ListName p_3 = (grammar.Absyn.ListName)((java_cup.runtime.Symbol) CUP$parser$stack.elementAt(CUP$parser$top-1)).value;
		 RESULT = new grammar.Absyn.RotationWithSymmetry(p_3); 
              CUP$parser$result = parser.getSymbolFactory().newSymbol("SymmetryOption",11, RESULT);
            }
          return CUP$parser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 25: // SymmetryOption ::= _SYMB_24 
            {
              grammar.Absyn.SymmetryOption RESULT =null;
		 RESULT = new grammar.Absyn.RotationSymmetry(); 
              CUP$parser$result = parser.getSymbolFactory().newSymbol("SymmetryOption",11, RESULT);
            }
          return CUP$parser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 24: // ListVerifierOption ::= ListVerifierOption VerifierOption _SYMB_3 
            {
              grammar.Absyn.ListVerifierOption RESULT =null;
		grammar.Absyn.ListVerifierOption p_1 = (grammar.Absyn.ListVerifierOption)((java_cup.runtime.Symbol) CUP$parser$stack.elementAt(CUP$parser$top-2)).value;
		grammar.Absyn.VerifierOption p_2 = (grammar.Absyn.VerifierOption)((java_cup.runtime.Symbol) CUP$parser$stack.elementAt(CUP$parser$top-1)).value;
		 RESULT = p_1; p_1.addLast(p_2); 
              CUP$parser$result = parser.getSymbolFactory().newSymbol("ListVerifierOption",10, RESULT);
            }
          return CUP$parser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 23: // ListVerifierOption ::= 
            {
              grammar.Absyn.ListVerifierOption RESULT =null;
		 RESULT = new grammar.Absyn.ListVerifierOption(); 
              CUP$parser$result = parser.getSymbolFactory().newSymbol("ListVerifierOption",10, RESULT);
            }
          return CUP$parser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 22: // VerifierOption ::= _SYMB_23 _SYMB_2 MyInteger 
            {
              grammar.Absyn.VerifierOption RESULT =null;
		String p_3 = (String)((java_cup.runtime.Symbol) CUP$parser$stack.peek()).value;
		 RESULT = new grammar.Absyn.ParLevel(p_3); 
              CUP$parser$result = parser.getSymbolFactory().newSymbol("VerifierOption",9, RESULT);
            }
          return CUP$parser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 21: // VerifierOption ::= _SYMB_19 _SYMB_2 MyInteger 
            {
              grammar.Absyn.VerifierOption RESULT =null;
		String p_3 = (String)((java_cup.runtime.Symbol) CUP$parser$stack.peek()).value;
		 RESULT = new grammar.Absyn.LogLevel(p_3); 
              CUP$parser$result = parser.getSymbolFactory().newSymbol("VerifierOption",9, RESULT);
            }
          return CUP$parser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 20: // VerifierOption ::= _SYMB_22 
            {
              grammar.Absyn.VerifierOption RESULT =null;
		 RESULT = new grammar.Absyn.NoPrecomputedInv(); 
              CUP$parser$result = parser.getSymbolFactory().newSymbol("VerifierOption",9, RESULT);
            }
          return CUP$parser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 19: // VerifierOption ::= _SYMB_21 
            {
              grammar.Absyn.VerifierOption RESULT =null;
		 RESULT = new grammar.Absyn.MonolithicWitness(); 
              CUP$parser$result = parser.getSymbolFactory().newSymbol("VerifierOption",9, RESULT);
            }
          return CUP$parser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 18: // VerifierOption ::= _SYMB_28 
            {
              grammar.Absyn.VerifierOption RESULT =null;
		 RESULT = new grammar.Absyn.UseRankingFunctions(); 
              CUP$parser$result = parser.getSymbolFactory().newSymbol("VerifierOption",9, RESULT);
            }
          return CUP$parser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 17: // VerifierOption ::= _SYMB_16 _SYMB_2 MyInteger 
            {
              grammar.Absyn.VerifierOption RESULT =null;
		String p_3 = (String)((java_cup.runtime.Symbol) CUP$parser$stack.peek()).value;
		 RESULT = new grammar.Absyn.ExplicitChecks(p_3); 
              CUP$parser$result = parser.getSymbolFactory().newSymbol("VerifierOption",9, RESULT);
            }
          return CUP$parser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 16: // VerifierOption ::= _SYMB_26 _SYMB_2 ListSymmetryOption 
            {
              grammar.Absyn.VerifierOption RESULT =null;
		grammar.Absyn.ListSymmetryOption p_3 = (grammar.Absyn.ListSymmetryOption)((java_cup.runtime.Symbol) CUP$parser$stack.peek()).value;
		 RESULT = new grammar.Absyn.SymmetryOptions(p_3); 
              CUP$parser$result = parser.getSymbolFactory().newSymbol("VerifierOption",9, RESULT);
            }
          return CUP$parser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 15: // VerifierOption ::= _SYMB_18 _SYMB_2 MyInteger _SYMB_6 MyInteger 
            {
              grammar.Absyn.VerifierOption RESULT =null;
		String p_3 = (String)((java_cup.runtime.Symbol) CUP$parser$stack.elementAt(CUP$parser$top-2)).value;
		String p_5 = (String)((java_cup.runtime.Symbol) CUP$parser$stack.peek()).value;
		 RESULT = new grammar.Absyn.NumOfInitStatesAutomatonGuess(p_3,p_5); 
              CUP$parser$result = parser.getSymbolFactory().newSymbol("VerifierOption",9, RESULT);
            }
          return CUP$parser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 14: // VerifierOption ::= _SYMB_14 _SYMB_2 MyInteger _SYMB_6 MyInteger 
            {
              grammar.Absyn.VerifierOption RESULT =null;
		String p_3 = (String)((java_cup.runtime.Symbol) CUP$parser$stack.elementAt(CUP$parser$top-2)).value;
		String p_5 = (String)((java_cup.runtime.Symbol) CUP$parser$stack.peek()).value;
		 RESULT = new grammar.Absyn.NumOfStatesAutomatonGuess(p_3,p_5); 
              CUP$parser$result = parser.getSymbolFactory().newSymbol("VerifierOption",9, RESULT);
            }
          return CUP$parser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 13: // VerifierOption ::= _SYMB_27 _SYMB_2 MyInteger _SYMB_6 MyInteger 
            {
              grammar.Absyn.VerifierOption RESULT =null;
		String p_3 = (String)((java_cup.runtime.Symbol) CUP$parser$stack.elementAt(CUP$parser$top-2)).value;
		String p_5 = (String)((java_cup.runtime.Symbol) CUP$parser$stack.peek()).value;
		 RESULT = new grammar.Absyn.NumOfStatesTransducerGuess(p_3,p_5); 
              CUP$parser$result = parser.getSymbolFactory().newSymbol("VerifierOption",9, RESULT);
            }
          return CUP$parser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 12: // AutomataAcceptingsRule ::= _SYMB_13 _SYMB_2 ListName _SYMB_3 
            {
              grammar.Absyn.AutomataAcceptingsRule RESULT =null;
		grammar.Absyn.ListName p_3 = (grammar.Absyn.ListName)((java_cup.runtime.Symbol) CUP$parser$stack.elementAt(CUP$parser$top-1)).value;
		 RESULT = new grammar.Absyn.AutomataAcceptings(p_3); 
              CUP$parser$result = parser.getSymbolFactory().newSymbol("AutomataAcceptingsRule",8, RESULT);
            }
          return CUP$parser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 11: // AutomataTransitionRule ::= Name _SYMB_4 Name 
            {
              grammar.Absyn.AutomataTransitionRule RESULT =null;
		grammar.Absyn.Name p_1 = (grammar.Absyn.Name)((java_cup.runtime.Symbol) CUP$parser$stack.elementAt(CUP$parser$top-2)).value;
		grammar.Absyn.Name p_3 = (grammar.Absyn.Name)((java_cup.runtime.Symbol) CUP$parser$stack.peek()).value;
		 RESULT = new grammar.Absyn.AutomataEmptyTransition(p_1,p_3); 
              CUP$parser$result = parser.getSymbolFactory().newSymbol("AutomataTransitionRule",7, RESULT);
            }
          return CUP$parser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 10: // AutomataTransitionRule ::= Name _SYMB_4 Name Name 
            {
              grammar.Absyn.AutomataTransitionRule RESULT =null;
		grammar.Absyn.Name p_1 = (grammar.Absyn.Name)((java_cup.runtime.Symbol) CUP$parser$stack.elementAt(CUP$parser$top-3)).value;
		grammar.Absyn.Name p_3 = (grammar.Absyn.Name)((java_cup.runtime.Symbol) CUP$parser$stack.elementAt(CUP$parser$top-1)).value;
		grammar.Absyn.Name p_4 = (grammar.Absyn.Name)((java_cup.runtime.Symbol) CUP$parser$stack.peek()).value;
		 RESULT = new grammar.Absyn.AutomataTransition(p_1,p_3,p_4); 
              CUP$parser$result = parser.getSymbolFactory().newSymbol("AutomataTransitionRule",7, RESULT);
            }
          return CUP$parser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 9: // AutomataInitRule ::= _SYMB_17 _SYMB_2 Name _SYMB_3 
            {
              grammar.Absyn.AutomataInitRule RESULT =null;
		grammar.Absyn.Name p_3 = (grammar.Absyn.Name)((java_cup.runtime.Symbol) CUP$parser$stack.elementAt(CUP$parser$top-1)).value;
		 RESULT = new grammar.Absyn.AutomataInitialState(p_3); 
              CUP$parser$result = parser.getSymbolFactory().newSymbol("AutomataInitRule",6, RESULT);
            }
          return CUP$parser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 8: // AutomatonRule ::= _SYMB_0 AutomataInitRule ListAutomataTransitionRule AutomataAcceptingsRule _SYMB_1 
            {
              grammar.Absyn.AutomatonRule RESULT =null;
		grammar.Absyn.AutomataInitRule p_2 = (grammar.Absyn.AutomataInitRule)((java_cup.runtime.Symbol) CUP$parser$stack.elementAt(CUP$parser$top-3)).value;
		grammar.Absyn.ListAutomataTransitionRule p_3 = (grammar.Absyn.ListAutomataTransitionRule)((java_cup.runtime.Symbol) CUP$parser$stack.elementAt(CUP$parser$top-2)).value;
		grammar.Absyn.AutomataAcceptingsRule p_4 = (grammar.Absyn.AutomataAcceptingsRule)((java_cup.runtime.Symbol) CUP$parser$stack.elementAt(CUP$parser$top-1)).value;
		 RESULT = new grammar.Absyn.Automaton(p_2,p_3,p_4); 
              CUP$parser$result = parser.getSymbolFactory().newSymbol("AutomatonRule",5, RESULT);
            }
          return CUP$parser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 7: // AcceptingRule ::= _SYMB_13 _SYMB_2 ListName _SYMB_3 
            {
              grammar.Absyn.AcceptingRule RESULT =null;
		grammar.Absyn.ListName p_3 = (grammar.Absyn.ListName)((java_cup.runtime.Symbol) CUP$parser$stack.elementAt(CUP$parser$top-1)).value;
		 RESULT = new grammar.Absyn.TransducerAccepting(p_3); 
              CUP$parser$result = parser.getSymbolFactory().newSymbol("AcceptingRule",4, RESULT);
            }
          return CUP$parser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 6: // TransitionRule ::= _SYMB_20 _SYMB_2 ListName 
            {
              grammar.Absyn.TransitionRule RESULT =null;
		grammar.Absyn.ListName p_3 = (grammar.Absyn.ListName)((java_cup.runtime.Symbol) CUP$parser$stack.peek()).value;
		 RESULT = new grammar.Absyn.LoopingTransition(p_3); 
              CUP$parser$result = parser.getSymbolFactory().newSymbol("TransitionRule",3, RESULT);
            }
          return CUP$parser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 5: // TransitionRule ::= Name _SYMB_4 Name 
            {
              grammar.Absyn.TransitionRule RESULT =null;
		grammar.Absyn.Name p_1 = (grammar.Absyn.Name)((java_cup.runtime.Symbol) CUP$parser$stack.elementAt(CUP$parser$top-2)).value;
		grammar.Absyn.Name p_3 = (grammar.Absyn.Name)((java_cup.runtime.Symbol) CUP$parser$stack.peek()).value;
		 RESULT = new grammar.Absyn.EmptyTransition(p_1,p_3); 
              CUP$parser$result = parser.getSymbolFactory().newSymbol("TransitionRule",3, RESULT);
            }
          return CUP$parser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 4: // TransitionRule ::= Name _SYMB_4 Name Name _SYMB_5 Name 
            {
              grammar.Absyn.TransitionRule RESULT =null;
		grammar.Absyn.Name p_1 = (grammar.Absyn.Name)((java_cup.runtime.Symbol) CUP$parser$stack.elementAt(CUP$parser$top-5)).value;
		grammar.Absyn.Name p_3 = (grammar.Absyn.Name)((java_cup.runtime.Symbol) CUP$parser$stack.elementAt(CUP$parser$top-3)).value;
		grammar.Absyn.Name p_4 = (grammar.Absyn.Name)((java_cup.runtime.Symbol) CUP$parser$stack.elementAt(CUP$parser$top-2)).value;
		grammar.Absyn.Name p_6 = (grammar.Absyn.Name)((java_cup.runtime.Symbol) CUP$parser$stack.peek()).value;
		 RESULT = new grammar.Absyn.FulTransition(p_1,p_3,p_4,p_6); 
              CUP$parser$result = parser.getSymbolFactory().newSymbol("TransitionRule",3, RESULT);
            }
          return CUP$parser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 3: // InitRule ::= _SYMB_17 _SYMB_2 Name _SYMB_3 
            {
              grammar.Absyn.InitRule RESULT =null;
		grammar.Absyn.Name p_3 = (grammar.Absyn.Name)((java_cup.runtime.Symbol) CUP$parser$stack.elementAt(CUP$parser$top-1)).value;
		 RESULT = new grammar.Absyn.TransducerInitialState(p_3); 
              CUP$parser$result = parser.getSymbolFactory().newSymbol("InitRule",2, RESULT);
            }
          return CUP$parser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 2: // TransducerRule ::= _SYMB_0 InitRule ListTransitionRule AcceptingRule _SYMB_1 
            {
              grammar.Absyn.TransducerRule RESULT =null;
		grammar.Absyn.InitRule p_2 = (grammar.Absyn.InitRule)((java_cup.runtime.Symbol) CUP$parser$stack.elementAt(CUP$parser$top-3)).value;
		grammar.Absyn.ListTransitionRule p_3 = (grammar.Absyn.ListTransitionRule)((java_cup.runtime.Symbol) CUP$parser$stack.elementAt(CUP$parser$top-2)).value;
		grammar.Absyn.AcceptingRule p_4 = (grammar.Absyn.AcceptingRule)((java_cup.runtime.Symbol) CUP$parser$stack.elementAt(CUP$parser$top-1)).value;
		 RESULT = new grammar.Absyn.Transducer(p_2,p_3,p_4); 
              CUP$parser$result = parser.getSymbolFactory().newSymbol("TransducerRule",1, RESULT);
            }
          return CUP$parser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 1: // ModelRule ::= _SYMB_9 AutomatonRule MaybeClosed _SYMB_12 TransducerRule _SYMB_8 AutomatonRule _SYMB_10 AutomatonRule _SYMB_11 AutomatonRule ListVerifierOption 
            {
              grammar.Absyn.ModelRule RESULT =null;
		grammar.Absyn.AutomatonRule p_2 = (grammar.Absyn.AutomatonRule)((java_cup.runtime.Symbol) CUP$parser$stack.elementAt(CUP$parser$top-10)).value;
		grammar.Absyn.MaybeClosed p_3 = (grammar.Absyn.MaybeClosed)((java_cup.runtime.Symbol) CUP$parser$stack.elementAt(CUP$parser$top-9)).value;
		grammar.Absyn.TransducerRule p_5 = (grammar.Absyn.TransducerRule)((java_cup.runtime.Symbol) CUP$parser$stack.elementAt(CUP$parser$top-7)).value;
		grammar.Absyn.AutomatonRule p_7 = (grammar.Absyn.AutomatonRule)((java_cup.runtime.Symbol) CUP$parser$stack.elementAt(CUP$parser$top-5)).value;
		grammar.Absyn.AutomatonRule p_9 = (grammar.Absyn.AutomatonRule)((java_cup.runtime.Symbol) CUP$parser$stack.elementAt(CUP$parser$top-3)).value;
		grammar.Absyn.AutomatonRule p_11 = (grammar.Absyn.AutomatonRule)((java_cup.runtime.Symbol) CUP$parser$stack.elementAt(CUP$parser$top-1)).value;
		grammar.Absyn.ListVerifierOption p_12 = (grammar.Absyn.ListVerifierOption)((java_cup.runtime.Symbol) CUP$parser$stack.peek()).value;
		 RESULT = new grammar.Absyn.Model(p_2,p_3,p_5,p_7,p_9,p_11,p_12); 
              CUP$parser$result = parser.getSymbolFactory().newSymbol("ModelRule",0, RESULT);
            }
          return CUP$parser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 0: // $START ::= ModelRule EOF 
            {
              Object RESULT =null;
		grammar.Absyn.ModelRule start_val = (grammar.Absyn.ModelRule)((java_cup.runtime.Symbol) CUP$parser$stack.elementAt(CUP$parser$top-1)).value;
		RESULT = start_val;
              CUP$parser$result = parser.getSymbolFactory().newSymbol("$START",0, RESULT);
            }
          /* ACCEPT */
          CUP$parser$parser.done_parsing();
          return CUP$parser$result;

          /* . . . . . .*/
          default:
            throw new Exception(
               "Invalid action number found in internal parse table");

        }
    }
}

