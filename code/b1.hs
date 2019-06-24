module Main where

import Codec.Binary.UTF8.String as Word
import Control.Concurrent.STM.TVar
import Control.Concurrent.STM
import Control.Concurrent
import Control.Exception
import Control.Monad.Fix (fix)
import Control.Monad.STM
import Control.Monad
import Data.Bits
import Data.ByteString.Lazy.Char8 as B (pack, unpack, ByteString)
import Data.Digest.Pure.SHA
import Data.IP
import Data.List as List
import Data.List.Split
import Data.Strings
import Data.Text.Encoding
import Data.Time.Clock.POSIX
import Data.Word
import GHC.Conc
import Network.Socket
import System.Environment
import System.Exit
import System.IO

data Block = Block { index :: Int,
                     prehash :: String,
                     timestamp :: Int,
                     bdata :: String,
                     psol :: Int,
                     bhash :: String} deriving (Show)

type Msg = (Int, String)
type Unionbc = TVar [Block]

challengeL = 4

newUnionbc :: [Block] -> IO Unionbc
newUnionbc blockchain = newTVarIO blockchain

writeUBC :: Unionbc -> [Block] -> STM ()
writeUBC cbc nbc = writeTVar cbc nbc

tupToList :: (a,a,a,a) -> [a]
tupToList (a,b,c,d) = [a,b,c,d]

listToTup :: [a] -> (a,a,a,a)
listToTup [a,b,c,d] = (a,b,c,d)

addBlock :: Block -> [Block] -> IO [Block]
addBlock elem list =
  do let nlist = elem : list
     return (nlist)

checkSolution :: String -> String -> Int -> IO (Bool)
checkSolution prehash bdata psol =
  do let nhash = showDigest $ sha256 $ B.pack $ bdata ++ show psol
     let prelength = length prehash
     let tough = challengeL
     let prob = drop (prelength - tough) prehash
     let ncomp = take tough nhash
     print (">> This is last 4 digets of prehash : " ++ prob)
     print (">> This is first 4 digest of newhash: "++ ncomp)
     if prob == ncomp
       then return True
       else return False


checkChain2 :: String -> [Block] -> IO (Bool)
checkChain2 lastHash blockChain =
  do if length blockChain > 0
       then do let lastB = last blockChain
               let pprehash = prehash lastB
               let nhash = bhash lastB
               let nbdata = bdata lastB
               let solver = psol lastB
               let hashed = showDigest $ sha256 $ B.pack $ nbdata ++ show solver
               let pnull = strNull pprehash
               chainOK <- case lastHash of
                            "" -> return True
                            _ -> if not pnull && lastHash == pprehash
                                 then return True
                                 else return False
               result <- checkSolution pprehash nbdata solver
               if result && (hashed == nhash) && chainOK
                 then do let restChain = init blockChain
                         result <- checkChain2 nhash restChain
                         return result
               else return False
     else return True

checkChain :: [Block] -> IO (Bool)
checkChain blockchain =
  do checked <- checkChain2 "" blockchain
     return checked
       

hashblock :: String -> String -> Int -> IO (String, Int)
hashblock prehash bdata psol =
  do result <- checkSolution prehash bdata psol
     if result
       then do let hashed = showDigest $ sha256 $ B.pack $ bdata ++ show psol
               return (hashed, psol)
       else do let npsol = psol + 1
               hashblock prehash bdata npsol

-- Creates a new block given some data (bdata), a timestamp and the blockchain
-- of which it should be inserted into
createBlock :: String -> Int -> [Block] -> IO (Block) 
createBlock bdata timestamp blockchain =
  do if length blockchain > 0
       then do let lastB = head blockchain
               let lindex = index lastB
               let nprehash = bhash lastB
               (nhash, psol) <- hashblock nprehash bdata 0
               let nblock = Block (lindex+1) nprehash timestamp bdata psol nhash
               return (nblock)
       else do let lindex = 0
               let firstprehash = showDigest $ sha256 $ B.pack "0"
               (nprehash, presol) <- hashblock firstprehash bdata 0
               (nhash,psol) <- hashblock nprehash bdata 0
               let nblock = Block lindex nprehash timestamp bdata psol nhash
               return (nblock)

addData :: String -> [Block] -> IO [Block]
addData bdata blockchain =
  do times <- round `fmap` getPOSIXTime
     nblock <- createBlock bdata times blockchain
     nlist <- addBlock nblock blockchain
     return nlist

mainLoop :: Socket -> Chan Msg -> Unionbc -> Int -> IO ()
mainLoop sock chan universalBC msgNum= do
  conn <- accept sock -- accept a connection and handle it
  forkIO (runConn conn chan universalBC msgNum)
  mainLoop sock chan universalBC $! msgNum + 1-- repeat

getChain :: [Block] -> String
getChain bchain =
  do if length bchain > 0
       then do let lastB = head bchain
               let lindex = index lastB
               let nprehash = prehash lastB
               let time = timestamp lastB
               let nhash = bhash lastB
               let nbdata = bdata lastB
               let solver = psol lastB
               let cblock = " ^^ [ ID: "++ show lindex ++ ", PreHash: " ++ nprehash ++ ", Timestamp: " ++ show time ++", Hash: " ++ nhash ++", Data: " ++ nbdata ++ ", Problem solver: "++ show solver ++ "] \n"
               let restc = getChain (tail bchain)
               nress <- cblock ++ restc
               return (nress)
       else return ' '

broadChain :: [Block] -> String
broadChain bchain =
  do if length bchain > 0
       then do let lastB = head bchain
               let lindex = index lastB
               let nprehash = prehash lastB
               let time = timestamp lastB
               let nhash = bhash lastB
               let nbdata = bdata lastB
               let solver = psol lastB
               let cblock = show lindex ++ "," ++ nprehash ++ "," ++ show time ++"," ++ nhash ++"," ++ nbdata ++ "," ++ show solver ++ "|"
               let restc = broadChain (tail bchain)
               nress <- cblock ++ restc
               return (nress)
       else return ' '

readchain2 :: [String] -> IO [Block]
readchain2 bcstring = do
  let nchain = []
  if length bcstring > 0
    then do let lastb = splitOn "," $ head bcstring
            let restb = tail bcstring
            let lindex = read $ lastb!!0
            let nprehash = lastb!!1
            let time = read $ lastb!!2
            let nhash = lastb!!3
            let nbdata = lastb!!4
            let solver = read $ lastb!!5
            let nblock = Block lindex nprehash time nbdata solver nhash
            let nbc = nblock : nchain
            rb <- readchain2 restb
            return $ nbc ++ rb
    else return nchain
            

readChain :: String -> IO [Block]
readChain bcstring = do
  let splitbc = init $ splitOn "|" bcstring
  nblockchain <- readchain2 splitbc
  return nblockchain
  
sloop :: (Handle, Chan Msg, Int) -> IO ()
sloop = fix $ \loop (hdl, chan, msgNum) ->
                do let broadcast msg = writeChan chan (msgNum, msg)
                   line <- liftM List.init (hGetLine hdl)
                   case line of
                     "quit" -> return ()
                     _ -> do broadcast (line)
                             print (">> server broadcasting")  >> loop (hdl, chan, msgNum)

loops :: (Handle, [Block], Chan Msg, Unionbc, Int) -> IO ()
loops = fix $ \loop (hdl, cbc, chan, universalBC, msgNum) -> do
  let broadcast msg = writeChan chan (msgNum, msg)
  line <- liftM List.init (hGetLine hdl)
  let linput = words line
  let count = length linput
  let command = linput!!0
  case command of
    "quit" -> do hPutStrLn hdl ">> Bye!"
                 return ()
    "bc" -> do if count > 1
                 then do let scommand = linput!!1
                         case scommand of
                           "show" -> do hPutStrLn hdl (">> your chain: \n" ++ getChain cbc)
                                        hPutStrLn hdl (">> What is your next command?") >> loop (hdl, cbc, chan, universalBC, msgNum)
                           "broadcast" -> do hPutStrLn hdl (">> broadcasting your blockchain:")
                                             let bcstring = broadChain cbc
                                             broadcast ("<BC> "++ bcstring )
                                             hPutStrLn hdl (">> What is your next command?") >> loop (hdl, cbc, chan, universalBC, msgNum)
                           "add" -> do let ns = cbc
                                       hPutStrLn hdl ">> Type the string to be stored:"
                                       ndata <- liftM List.init (hGetLine hdl)
                                       hPutStrLn hdl ">> Mining a new block, please wait..."
                                       ns <- addData ndata (cbc)
                                       let bsl = length ns
                                       hPutStrLn hdl (">> data added to your blockchain! size : "++ show bsl)
                                       hPutStrLn hdl (">> What is your next command?") >> loop (hdl, ns, chan, universalBC, msgNum)
                           "update" -> do readbc <- atomically $ readTVar universalBC
                                          check <- checkChain readbc
                                          case check of
                                            False -> do hPutStrLn hdl (">> new Blockchain not secure, current blockchain is NOT updated ")
                                                        hPutStrLn hdl (">> What is your next command?") >> loop (hdl, cbc, chan, universalBC, msgNum)  
                                            True -> do hPutStrLn hdl (">> Blockchain has been updated!")
                                                       hPutStrLn hdl (">> What is your next command?") >> loop (hdl, readbc, chan, universalBC, msgNum)
                           _ -> hPutStrLn hdl (">> Following 'blockchain' (bc) commands are avaible: 'update', 'add', 'broadcast' and 'show'") >> loop (hdl, cbc, chan, universalBC, msgNum)
                 else hPutStrLn hdl (">> Following 'blockchain' (bc) commands are avaible: 'update', 'add', 'broadcast' and 'show'") >> loop (hdl, cbc, chan, universalBC, msgNum)
    "pbc" -> do if count > 1
                  then do let scommand = linput!!1
                          case scommand of
                            "show" -> do readbc <- atomically $ readTVar universalBC
                                         hPutStrLn hdl (">> Public chain: \n" ++ getChain readbc)
                                         hPutStrLn hdl (">> What is your next command?") >> loop (hdl, cbc, chan, universalBC, msgNum)
                            _ -> hPutStrLn hdl (">> Following 'public blockchain' (pbc) commands are avaible: 'show'") >> loop (hdl, cbc, chan, universalBC, msgNum)
                  else  hPutStrLn hdl (">> Following 'public blockchain' (pbc) commands are avaible: 'show'") >> loop (hdl, cbc, chan, universalBC, msgNum)
    "help" -> do if count > 1
                   then do let scommand = linput!!1
                           case scommand of
                             "pbc" -> hPutStrLn hdl (">> Public blockchain (pbc) commands concerns the latest publiced blockchain on the network") >> loop (hdl, cbc, chan, universalBC, msgNum)
                             "bc" -> hPutStrLn hdl (">> blockchain (bc) commands concerns the clients local blockchain") >> loop (hdl, cbc, chan, universalBC, msgNum)
                             "quit" -> hPutStrLn hdl (">> 'quit' command is used to exit tcp client, does not close server") >> loop (hdl, cbc, chan, universalBC, msgNum)
                             _ -> hPutStrLn hdl (">> Following commands are supported: 'pbc', 'bc', 'quit' and 'help'. Get further information by typing 'help <name of command>' ") >> loop (hdl, cbc, chan, universalBC, msgNum)
                   else hPutStrLn hdl (">> Following commands are supported: 'pbc', 'bc', 'quit' and 'help'. Get further information by typing 'help <name of command>' ") >> loop (hdl, cbc, chan, universalBC, msgNum)
    _ -> hPutStrLn hdl (">> Command is not recognized, type 'help' for more information") >> loop (hdl, cbc, chan, universalBC, msgNum)

strToAddr :: String -> IO (HostAddress)
strToAddr addr = do let nStrList = splitOn "." addr
                    let intList = map read nStrList
                    let newHost = toHostAddress $ toIPv4 $ intList
                    return newHost


serverloop = fix $ \loop (hdl, chan, msgNum) ->
  do let broadcast msg = writeChan chan (msgNum, msg)
     line <- (hGetLine hdl)
     case line of
       ">> Server or user connection (U/S)" -> hPutStrLn hdl "S\r" >> loop (hdl, chan, msgNum)
       ">> Please type 'U' for user or 'S' for server" -> hPutStrLn hdl "S\r" >> loop (hdl, chan, msgNum)
       "end" -> return ()
       _ -> do broadcast(line)
               print (">> Got line: "++line) >> loop (hdl, chan, msgNum)

runServerConn :: (Handle, Chan Msg, Int) -> IO ()
runServerConn = fix $ \loop (hdl, chan, msgNum) -> do
  let broadcast msg = writeChan chan (msgNum, msg)
  hSetBuffering hdl LineBuffering
  commLine <- dupChan chan
  -- fork off a thread for reading from the duplicated channel
  reader <- forkIO $ fix $ \loop ->
    do (nextNum, line) <- readChan commLine
       if (msgNum /= nextNum)
         then do let linput = words line
                 let command = linput!!0
                 case command of
                   "<BC>" -> do hPutStrLn hdl line  >> loop
                   _ -> print(">> Got Line: "++ line) >> loop
         else loop
  serverloop (hdl, chan, msgNum)
  killThread reader
  hClose hdl


runConn :: (Socket, SockAddr) -> Chan Msg -> Unionbc -> Int -> IO ()
runConn (sock, _) chan universalBC msgNum = do
  let blockchain = []
  let broadcast msg = writeChan chan (msgNum, msg)
  hdl <- socketToHandle sock ReadWriteMode
  hSetBuffering hdl LineBuffering
  print (">> trying to connect")
  hPutStrLn hdl ">> Server or user connection (U/S)"
  contyp <- fix $ \loop ->
    do nline <- hWaitForInput hdl 0
       if nline
         then do line <- liftM List.init (hGetLine hdl)
                 case line of
                   "U" -> return (line)
                   "S" -> return (line)
                   _ -> do hPutStrLn hdl
                             (">> Please type 'U' for user or 'S' for server")
                           print(">> input:'"++line++"'") >> loop
         else loop
  commLine <- dupChan chan
  if(contyp == "U")
    then do reader <- forkIO $ fix $ \loop ->
              do (nextNum, line) <- readChan commLine
                 if (msgNum /= nextNum) then do
                     let linput = words line
                     let command = linput!!0
                     case command of
                       "<BC>" -> do let bcstring = unwords $ tail linput
                                    readbc <- readChain bcstring
                                    print (readbc)
                                    atomically $ writeTVar universalBC readbc
                                    hPutStrLn hdl
                                      (">> new blockchain is avaible") >> loop
                       _ -> hPutStrLn hdl line >> loop
                   else loop
            loops (hdl, blockchain, chan, universalBC, msgNum)
            killThread reader
    else do print (">> Server tcp client connected")
            reader <- forkIO $ fix $ \loop ->
              do (nextNum, line) <- readChan commLine
                 if (msgNum /= nextNum) then do
                     let linput = words line
                     let command = linput!!0
                     case command of
                       "<BC>" -> do hPutStrLn hdl line  >> loop
                       _ -> print(">> Got Line: "++ line) >> loop
                   else loop
            sloop (hdl, chan, msgNum)
            killThread reader
  hClose hdl
  
main = do
  args <- getArgs
  let arglen = length args
  let arg1 = args!!0
  let arg2 = args!!1
  let port = fromInteger $ read $ head $ args :: PortNumber -- get port number from consol parameter
  customIP <- strToAddr arg2
  
  sock <- socket AF_INET Stream 0 -- create socket
  setSocketOption sock ReuseAddr 1 -- make socket immediately resuable
  bind sock (SockAddrInet port customIP) --liston on TCP port 4242
  listen sock 2

  universalBC <- newUnionbc []
  chan <- newChan
  
  forkIO $ fix $ \loop -> do
    (_, msg) <- readChan chan
    loop
    
  msNum <- if arglen > 2
           then do let ctcp = args!!2
                   let ipAddr = args!!3
                   nHost <- strToAddr ipAddr
                   let tcpPort = read ctcp :: PortNumber
                   sockS <- socket AF_INET Stream 0
                   tcphandle <- try $ connect sockS (SockAddrInet tcpPort nHost)
                   case tcphandle of
                     Left (SomeException e) -> do print(">> Couldn't Connect to "++ipAddr++" <<")
                                                  return 0
                     Right h -> do print(">> Connected to.. " ++ ipAddr++" <<")
                                   hdlS <- socketToHandle sockS ReadWriteMode
                                   forkIO $ runServerConn (hdlS, chan, 0)
                                   return 1
           else return 0
    
  mainLoop sock chan universalBC msNum
