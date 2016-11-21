module Main where


import System.IO ( stderr, hPutStrLn, stdout )
import qualified  Data.Text.IO as IOT
import qualified Data.Attoparsec.Text as AT
import qualified OmegaAutomata.Hoa as H
import Options.Applicative
import Options.Applicative.Extra


import Reduce

data ArgOpts = ArgOpts 
    { top :: Bool
    , todo :: String
    }

argOpts :: Parser ArgOpts
argOpts = ArgOpts
    <$>     switch
            (long "top"
            <> help "use reduction depending on the transition system of the automaton"
            )
        <*> strOption
            (long "do" 
            <> metavar "(split | combine | reduce | sat | irred | all)"
            <> help "apply one or all reductions"
            )

main = do
    args <- execParser $
        info (helper <*> argOpts) 
            (fullDesc <> progDesc "reduce the acceptance condition of a deterministic Rabin automaton" <> header "reducerabinpairs")
    t <- IOT.getContents
    case AT.parseOnly H.parseHoa t of
         Left s -> hPutStrLn stderr ("Parse failed: " ++ s)
         Right hoa -> 
            let dra = H.hoaToDRA hoa 
                -- reddra = red dra
                reddra = case todo args of
                    "reduce" -> 
                        if (top args) 
                           then 
                             if is_compact dra 
                                then top_reduce dra
                                else error "not compact"
                            else set_reduce dra
                    "split" -> 
                        if (top args) then top_split dra 
                                      else toDRA $ set_split dra                         
                    "combine" -> 
                        if (top args) 
                           then 
                             if is_scc dra
                                then top_combine dra
                                else error "not scc"
                           else set_combine dra
                    "sat" -> 
                        if (top args) 
                           then
                             if is_compact dra
                                then top_sat dra
                                else error "not compact"
                           else set_sat dra
                    "irred" -> 
                        if (top args) 
                           then toDRA $ top_irredundant $ toSDRA dra 
                           else set_irredundant dra
                    "all" -> 
                        let setdra = set_irredundant $ set_sat $ set_reduce dra
                            tspdra = set_irredundant $ top_split setdra
                            trdra = 
                                if is_compact tspdra 
                                    then set_irredundant $ top_reduce tspdra
                                    else error "top_reduce: not compact"
                            tsdra =
                                if is_compact trdra
                                   then top_sat trdra
                                   else error "top_sat: not compact"
                            ssdra = set_irredundant $ toDRA $ set_split tsdra
                            tirdra =
                                toDRA $ top_irredundant $ toSDRA ssdra
                            tcomb = 
                                if is_scc tirdra
                                   then set_irredundant $ top_combine tirdra
                                   else error "top_combine: not scc"
                        in set_irredundant $ set_combine tcomb
                      in hPutStrLn stdout $ H.toHoa $ H.draToHoa reddra
