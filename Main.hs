import qualified Data.Set as Set
import Data.Set (Set)

{-|
    This Denotes that if all the children derive F then the original expression
    is true.
-}
data Node = Val {value :: Char} | Node {children :: (Set Node)}
    deriving (Ord, Eq, Show)

{-----------------------------
    PARSER
------------------------------}

{-|
    e.g. the expression a->(b->c) will become
         ->
        /  \
       a    ->
           /  \
          b    c
-}
data ExpressionTree =   Literal {lValue :: Char} 
                        | Implication 
                            {left :: ExpressionTree,
                            right :: ExpressionTree}
    deriving (Ord, Eq, Show)

{-|
    Parses the expression tree. See documentation of ExpressionTree for example.
-}
parseExpressionTree :: String -> ExpressionTree
parseExpressionTree string
    | (length tokens) == 1      = Literal (head string)
    | otherwise                 = Implication 
                                    (parseExpressionTree (head tokens)) 
                                    ((parseExpressionTree . head . tail) tokens)
    where
        tokens = tokenize string

{-|
    Break down the expression into [expression_left, expression_right].
-}
tokenize :: String -> [String]
tokenize string
    | (length string) == 1      = [string]
    | (head string) /= '('      = [[(head string)], (stripParantheses . tail . tail . tail) string]
    | otherwise                 = tokenizeHelper 1 "" (tail string)
    where
        tokenizeHelper :: Int -> String -> String -> [String]
        tokenizeHelper nParantheses parsedString remainingString
            | nParantheses == 1 && (head remainingString) == ')'    
                = [parsedString, (stripParantheses . tail . tail . tail) remainingString]
            | (head remainingString) == '('                         
                = tokenizeHelper (nParantheses+1) (parsedString ++ "(") (tail remainingString)
            | (head remainingString) == ')'                         
                = tokenizeHelper (nParantheses-1) (parsedString ++ ")") (tail remainingString)
            | otherwise                                             
                = tokenizeHelper nParantheses (parsedString ++ [head remainingString]) (tail remainingString)
        stripParantheses string
            -- assuming that the expression is either a single character or a
            -- well-formed expression enclosed by brackets.
            -- Not like (a->b)->c
            | (head string) == '('  = (tail . init) string
            | otherwise             = string

{-|
    ExpressionTree : expression tree corresponding to "a->(b->c)"
    Node : {a, b, {c}}
           Parsed using the deduction theorem which says
           S |- a->b <=> S U {a} |- b
-}
parseNode :: ExpressionTree -> Node
--parseNode (Literal l) = (Node . Set.singleton . Node . Set.singleton. Val) l
--parseNode (Implication left right) = Node $ Set.insert (parseNode left) $ (children . parseNode) right
parseNode (Literal l) = Val l
parseNode (Implication left right@(Literal l)) = Node $ Set.insert (parseNode left) $ (children . doubleNegationWrap . parseNode) right
    where
        doubleNegationWrap :: Node -> Node
        doubleNegationWrap = Node . Set.singleton . Node . Set.singleton
parseNode (Implication left right) = Node $ Set.insert (parseNode left) $ (children . parseNode) right

{-----------------------------
    DEDUCTION
------------------------------}

{-|
    Node : node to be negated
    Node : the negated node. The output may not always be the most simplied
           form.
           for example : 
                negate a = {a}
                negate {a,b} = {{a,b}}
                negate {a} = a

-}
negateNode :: Node -> Node
negateNode (Node s)
    | (Set.size s) == 1         = Set.findMin s
    | otherwise                 = Node . Set.singleton $ Node s
negateNode node = Node $ Set.singleton node


{-|
    Set Node : facts
    Node : hypothesis
    Bool : whether the hypothesis can be derived from the facts
-}
isDeducible :: Set Node -> Node -> Bool
isDeducible facts hypothesis
    | Set.member hypothesis facts       = True
    | otherwise                         = not . isContradiction $ Set.insert (negateNode hypothesis) facts


{-|
    Set Node : statements
    Bool : whether the statements lead to a contradiction
-}
isContradiction :: Set Node -> Bool
isContradiction statements = or $ Set.map (\stmt -> derivesChildrenOf (Set.delete stmt statements) stmt) statements
    where
        {-|
            Set Node : facts
            Node : the node we're trying derive the children of
            Bool : false if the node has no children, true if all the children
                   can be derived from the facts.
        -}
        derivesChildrenOf :: Set Node -> Node -> Bool
        derivesChildrenOf _ (Val _) = False
        derivesChildrenOf facts (Node hypotheses) = and $ Set.map (isDeducible facts) hypotheses