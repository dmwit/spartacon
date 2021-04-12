{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}

module Main where

import Control.Applicative
import Control.Exception
import Control.Monad
import Control.Monad.Reader
import Control.Monad.State
import Data.Bits
import Data.Either.Validation
import Data.Foldable
import Data.Functor.Identity
import Data.List
import Data.Map (Map)
import Data.Maybe
import Data.Relation (Relation)
import Data.Set (Set)
import Data.Text (Text)
import Data.Traversable
import Graphics.X11.Xlib hiding (refreshKeyboardMapping)
import Graphics.X11.Xlib.Extras
import System.Exit
import System.IO
import Text.Printf

import qualified Config as C
import qualified Config.Schema as C
import qualified Data.Map as M
import qualified Data.Relation as R
import qualified Data.Set as S
import qualified Data.Text as T
import qualified Data.Text.IO as T

main :: IO ()
main = do
	config <- readConfiguration
	runSpartacon config $ do
		root <- askRoot
		refreshBindings
		x selectInput root keyPressMask
		suspend $ \ctx s -> allocaXEvent $ \evPtr -> resume ctx s . forever $ do
			x nextEvent evPtr
			ev <- io getEvent evPtr
			case ev of
				MappingNotifyEvent{} -> do
					io refreshKeyboardMapping ev
					km <- x reloadKeymap
					modify (\s -> s { keymap = km })
					refreshBindings
				KeyEvent{}
					| ev_event_type ev /= keyPress -> pure ()
					| otherwise -> do
						bs <- gets bindings
						io $ case M.lookup (ev_state ev, ev_keycode ev) bs of
							Just Quit -> exitWith ExitSuccess
							Just (Print t) -> T.putStr t >> hFlush stdout
							Nothing -> hPrintf stderr "WARNING: got key event with no corresponding binding: %s\n" (show ev)
				_ -> io hPrintf stderr "WARNING: ignoring unexpected X event %s\n" (show ev)

readConfiguration :: IO Configuration
readConfiguration = do
	t <- T.getContents
	v <- case C.parse t of
		Left err -> do
			hPrintf
				stderr
				"Formatting error in configuration. Check the syntax reference at:\nhttp://hackage.haskell.org/package/config-value/docs/Config.html\n\t%s\n"
				(displayException err)
			exitWith (ExitFailure 1)
		Right v -> pure v
	case C.loadValue C.anySpec v of
		Left err -> hPutStrLn stderr (displayException err) >> exitWith (ExitFailure 2)
		Right config -> pure config

data Configuration = Configuration
	{ ignoreMasks :: [KeyMask]
	, bindingRequests :: [(BindingRequest, Action)]
	} deriving (Eq, Ord, Read, Show)

data BindingRequest = BindingRequest
	{ modifier :: KeyMask
	, key :: Either KeySym KeyCode
	} deriving (Eq, Ord, Read, Show)

data Action = Quit | Print Text
	deriving (Eq, Ord, Read, Show)

data Context = Context
	{ configuration :: Configuration
	, display :: Display
	} deriving (Eq, Ord, Show)

data KeyboardState = KeyboardState
	{ keymap :: Relation KeyCode KeySym
	, bindings :: Map (KeyMask, KeyCode) Action
	} deriving (Eq, Ord, Show)

type Spartacon = ReaderT Context (StateT KeyboardState IO)

runSpartacon :: Configuration -> Spartacon a -> IO a
runSpartacon config act = do
	dpy <- openDisplay ""
	keys <- reloadKeymap dpy
	evalStateT (runReaderT act (Context config dpy)) (KeyboardState keys M.empty)

suspend :: (Context -> KeyboardState -> IO (a, KeyboardState)) -> Spartacon a
suspend f = ReaderT $ StateT . f

resume :: Context -> KeyboardState -> Spartacon a -> IO (a, KeyboardState)
resume ctx s act = runStateT (runReaderT act ctx) s

reloadKeymap :: Display -> IO (Relation KeyCode KeySym)
reloadKeymap dpy = do
	mapping <- for [lo..hi] $ \keycode ->
		for [0..3] $ \i ->
			(,) keycode <$> keycodeToKeysym dpy keycode i
	pure . R.fromList $
		[ (keycode, keysym)
		| pairs <- mapping
		, (keycode, keysym) <- pairs
		, keysym /= noSymbol
		]
	where
	(lo_, hi_) = displayKeycodes dpy
	[lo, hi] = map fromIntegral [lo_, hi_]

expandCodes ::
	Configuration ->
	Relation KeyCode KeySym ->
	[((BindingRequest, Action), (KeyMask, KeyCode))]
expandCodes conf mapping =
	[ (reqAct, (modifier req .|. extraMask, code))
	| extraMasks <- subsequences (ignoreMasks conf)
	, let extraMask = foldl' (.|.) 0 extraMasks
	, reqAct@(req, act) <- bindingRequests conf
	, code <- case key req of
		Right code -> [code]
		Left sym -> S.toList . R.lookupRan sym $ mapping
	]

checkCodes ::
	[(BindingRequest, Action)] ->
	[((BindingRequest, Action), (KeyMask, KeyCode))] ->
	( [(BindingRequest, Action)]
	, Map (KeyMask, KeyCode) (Set (BindingRequest, Action))
	, Map (KeyMask, KeyCode) Action
	)
checkCodes reqs expanded =
	( S.toList $ reqSet S.\\ foldMap sourceRequests mappings
	, runIdentity $ M.traverseMaybeWithKey keepDuplicates mappings
	, runIdentity $ M.traverseMaybeWithKey keepActions mappings
	) where
	mappings :: Map (KeyMask, KeyCode) (Map Action (Set BindingRequest))
	mappings = M.fromListWith (M.unionWith S.union)
		[ (binding, M.singleton act (S.singleton req))
		| ((req, act), binding) <- expanded
		]

	keepActions :: (KeyMask, KeyCode) -> Map Action (Set BindingRequest) -> Identity (Maybe Action)
	keepActions _ = Identity . fmap fst . M.lookupMin

	keepDuplicates :: (KeyMask, KeyCode) -> Map Action (Set BindingRequest) -> Identity (Maybe (Set (BindingRequest, Action)))
	keepDuplicates _ m = Identity $ if M.size m > 1
		then Just (sourceRequests m)
		else Nothing

	sourceRequests :: Map Action (Set BindingRequest) -> Set (BindingRequest, Action)
	sourceRequests = M.foldMapWithKey (\act -> S.map (flip (,) act))

	reqSet :: Set (BindingRequest, Action)
	reqSet = S.fromList reqs

computeCodes :: Configuration -> Relation KeyCode KeySym ->
	( [(BindingRequest, Action)]
	, Map (KeyMask, KeyCode) (Set (BindingRequest, Action))
	, Map (KeyMask, KeyCode) Action
	)
computeCodes conf = checkCodes (bindingRequests conf) . expandCodes conf

computeBindings :: Spartacon (Map (KeyMask, KeyCode) Action)
computeBindings = do
	conf <- asks configuration
	(unbound, ambiguous, bs) <- computeCodes conf <$> gets keymap
	unless (null unbound) $ do
		io hPutStrLn stderr "WARNING: No keys found for the following binding requests:"
		forM_ unbound $ io hPrintf stderr "\t%s\n" . pp
	unless (M.null ambiguous) $ do
		io hPutStrLn stderr "WARNING: Some binding requests conflict."
		flip M.traverseWithKey ambiguous $ \binding@(mask, code) reqs -> io $ do
			hPrintf stderr "\tThese binding requests are competing for mask %s, keycode %d"
				(reverse . drop 1 . reverse . pp $ mask)
				code
			for_ (M.lookup binding bs) $ hPrintf stderr " (winner: %s)" . pp
			hPutStrLn stderr ":"
			for_ reqs $ hPrintf stderr "\t\t%s\n" . pp
		pure ()
	pure bs

refreshBindings :: Spartacon ()
refreshBindings = do
	bs <- gets bindings
	bs' <- computeBindings
	root <- askRoot
	for_ (M.keysSet (bs M.\\ bs')) $ \(mask, code) -> x ungrabKey code mask root
	for_ (M.keysSet (bs' M.\\ bs)) $ \(mask, code) -> x grabKey code mask root False grabModeAsync grabModeAsync
	modify (\s -> s { bindings = bs' })

class PP a where pp :: a -> String

instance PP Action where
	pp Quit = "quit"
	pp (Print t) = show t

instance PP BindingRequest where
	pp (BindingRequest mask code) = case (pp mask, pp code) of
		-- atoms must start with a letter
		("", s@(c:_)) | c < 'A' || c > 'z' || (c > 'Z' && c < 'a')
			-> "B-" ++ s
		(s, s') -> s ++ s'

instance PP (Either KeySym KeyCode) where
	pp (Left sym) = keysymToString sym
	pp (Right code) = "." ++ show code

instance PP (BindingRequest, Action) where
	pp (req, action) = pp req ++ ": " ++ pp action

instance PP KeyMask where
	pp mask = concat $ zipWith
		(\label mask' -> if mask .&. mask' == 0 then "" else label ++ "-")
		-- TODO: numlock/alt might not be mod2Mask/mod1Mask
		["NL", "L", "C", "A", "S", "M3", "M4", "M5"]
		[mod2Mask, lockMask, controlMask, mod1Mask, shiftMask, mod3Mask, mod4Mask, mod5Mask]

askRoot :: Spartacon Window
askRoot = asks (defaultRootWindow . display)

instance C.HasSpec Configuration where
	anySpec = C.sectionsSpec "configuration" $ pure Configuration
		-- TODO: NL might not always be mod2Mask
		<*> (nub . fromMaybe [mod2Mask] <$> C.optSection' "ignore" (C.listSpec C.anySpec) "keymasks to ignore when deciding whether a keypress matches (default: NL)")
		<*> (fold <$> C.optSection' "bindings" bindingRequestsSpec "keys to watch for and the actions to take when they're pressed (default: no bindings)")

bindingRequestsSpec :: C.ValueSpec [(BindingRequest, Action)]
bindingRequestsSpec = C.customSpec
	"binding requests"
	(C.assocSpec C.anySpec)
	( ppParseError "binding requests"
	. traverse (\(req, act) -> flip (,) act <$> parseBindingRequest req)
	)

instance C.HasSpec Action where
	anySpec = (Quit <$ C.atomSpec "quit") C.<!> (Quit <$ C.atomSpec "exit")
	    C.<!> (Print <$> C.anySpec)

instance C.HasSpec KeyMask where
	anySpec = foldr1 (C.<!>) [mask <$ C.atomSpec label | (label, mask) <- modifierMap]

parseModifier :: Text -> Validation [(Text, [Text])] (Text, KeyMask)
parseModifier t = head $
	[ pure (T.drop (T.length t') t, m)
	| (t', m) <- modifierMap
	, t' `T.isPrefixOf` t
	] ++ [Failure [(t, fst <$> modifierMap)]]

parseOnlyModifier :: Text -> Validation [(Text, [Text])] KeyMask
parseOnlyModifier t = case parseModifier t of
	Success (t', m)
		| T.null t' -> pure m
		| otherwise -> Failure [(t', ["<end of string>"])]
	Failure errs -> Failure errs

parseKey :: Text -> Validation [(Text, [Text])] (Either KeySym KeyCode)
parseKey t
	| T.isPrefixOf "." t = case reads . tail . T.unpack $ t of
		(code, ""):_ -> pure (Right code)
		(_, unparsed):_ -> Failure [(T.pack unparsed, ["<end of string>"])]
		[] -> Failure [(T.drop 1 t, ["<number>"])]
	| otherwise = case stringToKeysym . T.unpack $ t of
		0 -> Failure [(t, ["<keysym string>"])]
		sym -> pure (Left sym)

parseBindingRequest :: Text -> Validation [(Text, [Text])] BindingRequest
parseBindingRequest t = case T.splitOn "-" t of
	[] -> Failure [(t, ["<anything>"])]
	ts -> pure BindingRequest
		<*> (foldr (.|.) noModMask <$> traverse parseOnlyModifier (init ts))
		<*> parseKey (last ts)

-- TODO: alt/numlock aren't necessarily M1/M2
modifierMap :: [(Text, KeyMask)]
modifierMap = concat . tail $ [undefined
	, "S" ~> shiftMask
	, "L" ~> lockMask
	, "C" ~> controlMask
	, "A" ~> mod1Mask
	, "M1" ~> mod1Mask
	, "NL" ~> mod2Mask
	, "M2" ~> mod2Mask
	, "M3" ~> mod3Mask
	, "M4" ~> mod4Mask
	, "M5" ~> mod5Mask
	, "B" ~> noModMask -- blank; needed to bind 1-9 or keycodes with no modifier, since atoms must start with a letter
	]
	where
	t ~> m = [(t, m), (T.toLower t, m)]

ppParseError :: Text -> Validation [(Text, [Text])] a -> Either Text a
ppParseError ty (Success a) = Right a
ppParseError ty (Failure errs) = Left . T.unlines . ("\tParsing of " <> ty <> " failed":) $
	[ msg
	| (t, expecteds) <- errs
	, msg <- ("\tat " <> t <> ", expected one of these:") : map ("\t\t"<>) expecteds
	]

class SpartaClass a where
	type Rebel a = r | r -> a
	x :: (Display -> a) -> Rebel a
	io :: a -> Rebel a

instance SpartaClass (IO a) where
	type Rebel (IO a) = Spartacon a
	x f = ask >>= liftIO . f . display
	io = liftIO

instance SpartaClass b => SpartaClass (a -> b) where
	type Rebel (a -> b) = a -> Rebel b
	x f = x . flip f
	io f = io . f
