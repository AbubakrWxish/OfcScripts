local StrToNumber = tonumber;
local Byte = string.byte;
local Char = string.char;
local Sub = string.sub;
local Subg = string.gsub;
local Rep = string.rep;
local Concat = table.concat;
local Insert = table.insert;
local LDExp = math.ldexp;
local GetFEnv = getfenv or function()
	return _ENV;
end;
local Setmetatable = setmetatable;
local PCall = pcall;
local Select = select;
local Unpack = unpack or table.unpack;
local ToNumber = tonumber;
local function VMCall(ByteString, vmenv, ...)
	local DIP = 1;
	local repeatNext;
	ByteString = Subg(Sub(ByteString, 5), "..", function(byte)
		if (Byte(byte, 2) == 81) then
			repeatNext = StrToNumber(Sub(byte, 1, 1));
			return "";
		else
			local a = Char(StrToNumber(byte, 16));
			if repeatNext then
				local b = Rep(a, repeatNext);
				repeatNext = nil;
				return b;
			else
				return a;
			end
		end
	end);
	local function gBit(Bit, Start, End)
		if End then
			local Res = (Bit / (2 ^ (Start - 1))) % (2 ^ (((End - 1) - (Start - 1)) + 1));
			return Res - (Res % 1);
		else
			local Plc = 2 ^ (Start - 1);
			return (((Bit % (Plc + Plc)) >= Plc) and 1) or 0;
		end
	end
	local function gBits8()
		local a = Byte(ByteString, DIP, DIP);
		DIP = DIP + 1;
		return a;
	end
	local function gBits16()
		local a, b = Byte(ByteString, DIP, DIP + 2);
		DIP = DIP + 2;
		return (b * 256) + a;
	end
	local function gBits32()
		local a, b, c, d = Byte(ByteString, DIP, DIP + 3);
		DIP = DIP + 4;
		return (d * 16777216) + (c * 65536) + (b * 256) + a;
	end
	local function gFloat()
		local Left = gBits32();
		local Right = gBits32();
		local IsNormal = 1;
		local Mantissa = (gBit(Right, 1, 20) * (2 ^ 32)) + Left;
		local Exponent = gBit(Right, 21, 31);
		local Sign = ((gBit(Right, 32) == 1) and -1) or 1;
		if (Exponent == 0) then
			if (Mantissa == 0) then
				return Sign * 0;
			else
				Exponent = 1;
				IsNormal = 0;
			end
		elseif (Exponent == 2047) then
			return ((Mantissa == 0) and (Sign * (1 / 0))) or (Sign * NaN);
		end
		return LDExp(Sign, Exponent - 1023) * (IsNormal + (Mantissa / (2 ^ 52)));
	end
	local function gString(Len)
		local Str;
		if not Len then
			Len = gBits32();
			if (Len == 0) then
				return "";
			end
		end
		Str = Sub(ByteString, DIP, (DIP + Len) - 1);
		DIP = DIP + Len;
		local FStr = {};
		for Idx = 1, #Str do
			FStr[Idx] = Char(Byte(Sub(Str, Idx, Idx)));
		end
		return Concat(FStr);
	end
	local gInt = gBits32;
	local function _R(...)
		return {...}, Select("#", ...);
	end
	local function Deserialize()
		local Instrs = {};
		local Functions = {};
		local Lines = {};
		local Chunk = {Instrs,Functions,nil,Lines};
		local ConstCount = gBits32();
		local Consts = {};
		for Idx = 1, ConstCount do
			local Type = gBits8();
			local Cons;
			if (Type == 1) then
				Cons = gBits8() ~= 0;
			elseif (Type == 2) then
				Cons = gFloat();
			elseif (Type == 3) then
				Cons = gString();
			end
			Consts[Idx] = Cons;
		end
		Chunk[3] = gBits8();
		for Idx = 1, gBits32() do
			local Descriptor = gBits8();
			if (gBit(Descriptor, 1, 1) == 0) then
				local Type = gBit(Descriptor, 2, 3);
				local Mask = gBit(Descriptor, 4, 6);
				local Inst = {gBits16(),gBits16(),nil,nil};
				if (Type == 0) then
					Inst[3] = gBits16();
					Inst[4] = gBits16();
				elseif (Type == 1) then
					Inst[3] = gBits32();
				elseif (Type == 2) then
					Inst[3] = gBits32() - (2 ^ 16);
				elseif (Type == 3) then
					Inst[3] = gBits32() - (2 ^ 16);
					Inst[4] = gBits16();
				end
				if (gBit(Mask, 1, 1) == 1) then
					Inst[2] = Consts[Inst[2]];
				end
				if (gBit(Mask, 2, 2) == 1) then
					Inst[3] = Consts[Inst[3]];
				end
				if (gBit(Mask, 3, 3) == 1) then
					Inst[4] = Consts[Inst[4]];
				end
				Instrs[Idx] = Inst;
			end
		end
		for Idx = 1, gBits32() do
			Functions[Idx - 1] = Deserialize();
		end
		return Chunk;
	end
	local function Wrap(Chunk, Upvalues, Env)
		local Instr = Chunk[1];
		local Proto = Chunk[2];
		local Params = Chunk[3];
		return function(...)
			local Instr = Instr;
			local Proto = Proto;
			local Params = Params;
			local _R = _R;
			local VIP = 1;
			local Top = -1;
			local Vararg = {};
			local Args = {...};
			local PCount = Select("#", ...) - 1;
			local Lupvals = {};
			local Stk = {};
			for Idx = 0, PCount do
				if (Idx >= Params) then
					Vararg[Idx - Params] = Args[Idx + 1];
				else
					Stk[Idx] = Args[Idx + 1];
				end
			end
			local Varargsz = (PCount - Params) + 1;
			local Inst;
			local Enum;
			while true do
				Inst = Instr[VIP];
				Enum = Inst[1];
				if (Enum <= 24) then
					if (Enum <= 11) then
						if (Enum <= 5) then
							if (Enum <= 2) then
								if (Enum <= 0) then
									Stk[Inst[2]][Inst[3]] = Inst[4];
								elseif (Enum == 1) then
									Stk[Inst[2]][Inst[3]] = Inst[4];
								else
									local A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							elseif (Enum <= 3) then
								Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
							elseif (Enum == 4) then
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]] = Upvalues[Inst[3]];
							end
						elseif (Enum <= 8) then
							if (Enum <= 6) then
								local A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
							elseif (Enum > 7) then
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							else
								local A = Inst[2];
								local B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							end
						elseif (Enum <= 9) then
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum > 10) then
							local A = Inst[2];
							local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
							local Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						else
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						end
					elseif (Enum <= 17) then
						if (Enum <= 14) then
							if (Enum <= 12) then
								local A = Inst[2];
								Stk[A] = Stk[A]();
							elseif (Enum > 13) then
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
							else
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						elseif (Enum <= 15) then
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Stk[A + 1]));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						elseif (Enum == 16) then
							do
								return;
							end
						else
							local A = Inst[2];
							Stk[A] = Stk[A]();
						end
					elseif (Enum <= 20) then
						if (Enum <= 18) then
							local A = Inst[2];
							local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
							local Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						elseif (Enum > 19) then
							if not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							Stk[Inst[2]] = {};
						end
					elseif (Enum <= 22) then
						if (Enum == 21) then
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						else
							local A = Inst[2];
							Stk[A](Stk[A + 1]);
						end
					elseif (Enum > 23) then
						if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					else
						VIP = Inst[3];
					end
				elseif (Enum <= 37) then
					if (Enum <= 30) then
						if (Enum <= 27) then
							if (Enum <= 25) then
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							elseif (Enum > 26) then
								local A = Inst[2];
								local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							else
								Stk[Inst[2]] = {};
							end
						elseif (Enum <= 28) then
							VIP = Inst[3];
						elseif (Enum == 29) then
							Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
						else
							Stk[Inst[2]] = Env[Inst[3]];
						end
					elseif (Enum <= 33) then
						if (Enum <= 31) then
							local NewProto = Proto[Inst[3]];
							local NewUvals;
							local Indexes = {};
							NewUvals = Setmetatable({}, {__index=function(_, Key)
								local Val = Indexes[Key];
								return Val[1][Val[2]];
							end,__newindex=function(_, Key, Value)
								local Val = Indexes[Key];
								Val[1][Val[2]] = Value;
							end});
							for Idx = 1, Inst[4] do
								VIP = VIP + 1;
								local Mvm = Instr[VIP];
								if (Mvm[1] == 34) then
									Indexes[Idx - 1] = {Stk,Mvm[3]};
								else
									Indexes[Idx - 1] = {Upvalues,Mvm[3]};
								end
								Lupvals[#Lupvals + 1] = Indexes;
							end
							Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
						elseif (Enum == 32) then
							local A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
						else
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						end
					elseif (Enum <= 35) then
						if (Enum > 34) then
							local A = Inst[2];
							local B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
						else
							Stk[Inst[2]] = Stk[Inst[3]];
						end
					elseif (Enum == 36) then
						local A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
					else
						local A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
					end
				elseif (Enum <= 43) then
					if (Enum <= 40) then
						if (Enum <= 38) then
							Stk[Inst[2]] = Upvalues[Inst[3]];
						elseif (Enum == 39) then
							if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local A = Inst[2];
							local C = Inst[4];
							local CB = A + 2;
							local Result = {Stk[A](Stk[A + 1], Stk[CB])};
							for Idx = 1, C do
								Stk[CB + Idx] = Result[Idx];
							end
							local R = Result[1];
							if R then
								Stk[CB] = R;
								VIP = Inst[3];
							else
								VIP = VIP + 1;
							end
						end
					elseif (Enum <= 41) then
						Stk[Inst[2]] = Env[Inst[3]];
					elseif (Enum > 42) then
						local A = Inst[2];
						Stk[A](Stk[A + 1]);
					else
						Stk[Inst[2]] = Inst[3];
					end
				elseif (Enum <= 46) then
					if (Enum <= 44) then
						local A = Inst[2];
						local C = Inst[4];
						local CB = A + 2;
						local Result = {Stk[A](Stk[A + 1], Stk[CB])};
						for Idx = 1, C do
							Stk[CB + Idx] = Result[Idx];
						end
						local R = Result[1];
						if R then
							Stk[CB] = R;
							VIP = Inst[3];
						else
							VIP = VIP + 1;
						end
					elseif (Enum > 45) then
						if not Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					else
						local A = Inst[2];
						local Results, Limit = _R(Stk[A](Stk[A + 1]));
						Top = (Limit + A) - 1;
						local Edx = 0;
						for Idx = A, Top do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
					end
				elseif (Enum <= 48) then
					if (Enum > 47) then
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
					else
						do
							return;
						end
					end
				elseif (Enum > 49) then
					local NewProto = Proto[Inst[3]];
					local NewUvals;
					local Indexes = {};
					NewUvals = Setmetatable({}, {__index=function(_, Key)
						local Val = Indexes[Key];
						return Val[1][Val[2]];
					end,__newindex=function(_, Key, Value)
						local Val = Indexes[Key];
						Val[1][Val[2]] = Value;
					end});
					for Idx = 1, Inst[4] do
						VIP = VIP + 1;
						local Mvm = Instr[VIP];
						if (Mvm[1] == 34) then
							Indexes[Idx - 1] = {Stk,Mvm[3]};
						else
							Indexes[Idx - 1] = {Upvalues,Mvm[3]};
						end
						Lupvals[#Lupvals + 1] = Indexes;
					end
					Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
				else
					Stk[Inst[2]] = Inst[3];
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!373Q00030A3Q006C6F6164737472696E6703043Q0067616D6503073Q00482Q747047657403493Q00682Q7470733A2Q2F6769746875622E636F6D2F64617769642D736372697074732F466C75656E742F72656C65617365732F6C61746573742F646F776E6C6F61642F6D61696E2E6C7561030C3Q0043726561746557696E646F7703053Q005469746C65030F3Q00416E696D616C20486F73706974616C03083Q005375625469746C65030F3Q0062792041627562616B72577869736803083Q005461625769647468026Q00644003043Q0053697A6503053Q005544696D32030A3Q0066726F6D4F2Q66736574025Q00E07F40025Q00A0744003073Q00416372796C6963010003053Q005468656D6503043Q004461726B030B3Q004D696E696D697A654B657903043Q00456E756D03073Q004B6579436F646503013Q004D03043Q004D61696E03063Q00412Q64546162030E3Q00D093D0BBD0B0D0B2D0BDD18BD0B903043Q0049636F6E03053Q00686F75736503083Q0053652Q74696E677303123Q00D09DD0B0D181D182D180D0BED0B9D0BAD0B803083Q0073652Q74696E6773030A3Q004765745365727669636503073Q00506C6179657273030B3Q004C6F63616C506C6179657203093Q00412Q64536C69646572030B3Q0053702Q6564536C6964657203053Q0053702Q6564030B3Q004465736372697074696F6E03133Q0053657420796F75722077616C6B73702Q65642E03073Q0044656661756C74026Q0030402Q033Q004D696E2Q033Q004D6178025Q00C0624003083Q00526F756E64696E67026Q00F03F03083Q0043612Q6C6261636B03093Q00412Q64546F2Q676C6503093Q00496E7374616E742Q50031D3Q00D091D18BD181D182D180D18BD0B520D0BFD180D0BED0BCD0BFD182D18B03093Q004F6E4368616E67656403093Q00457370546F2Q676C65031F3Q00D09FD0BED0BAD0B0D0B7D0B0D182D18C20D0B8D0B3D180D0BED0BAD0BED0B203093Q0053656C65637454616200563Q00121E3Q00013Q00121E000100023Q00202300010001000300122A000300044Q0021000100034Q000E5Q00022Q00113Q0001000200202300013Q00052Q001300033Q00070030010003000600070030010003000800090030010003000A000B00121E0004000D3Q00201900040004000E00122A0005000F3Q00122A000600104Q000D00040006000200100A0003000C000400300100030011001200300100030013001400121E000400163Q00201900040004001700201900040004001800100A0003001500042Q000D0001000300022Q001300023Q000200202300030001001A2Q001300053Q000200300100050006001B0030010005001C001D2Q000D00030005000200100A00020019000300202300030001001A2Q001300053Q000200300100050006001F0030010005001C00202Q000D00030005000200100A0002001E000300121E000300023Q00202300030003002100122A000500224Q000D00030005000200201900040003002300021D00055Q00021D000600013Q00201900070002001900202300070007002400122A000900254Q0013000A3Q0007003001000A00060026003001000A00270028003001000A0029002A003001000A002B002A003001000A002C002D003001000A002E002F00021D000B00023Q00100A000A0030000B2Q000D0007000A000200201900080002001900202300080008003100122A000A00324Q0013000B3Q0002003001000B00060033003001000B002900122Q000D0008000B000200202300090008003400021D000B00034Q00020009000B000100201900090002001900202300090009003100122A000B00354Q0013000C3Q0002003001000C00060036003001000C002900122Q000D0009000C0002002023000A0009003400061F000C0004000100042Q00223Q00034Q00223Q00044Q00223Q00054Q00223Q00064Q0002000A000C0001002023000A0001003700122A000C002F4Q0002000A000C00012Q00103Q00013Q00053Q00143Q00030E3Q0046696E6446697273744368696C6403133Q00506C617965724553505F486967686C6967687403083Q00496E7374616E63652Q033Q006E657703093Q00486967686C6967687403043Q004E616D6503073Q0041646F726E2Q6503063Q00506172656E7403093Q0046692Q6C436F6C6F7203063Q00436F6C6F723303073Q0066726F6D524742026Q005440026Q006940026Q005E40030C3Q004F75746C696E65436F6C6F72025Q00E06F4003103Q0046692Q6C5472616E73706172656E6379026Q00E03F03133Q004F75746C696E655472616E73706172656E6379028Q00011D3Q00202300013Q000100122A000300024Q000D00010003000200062E0001001C000100010004173Q001C000100121E000100033Q00201900010001000400122A000200054Q002000010002000200300100010006000200100A000100073Q00100A000100083Q00121E0002000A3Q00201900020002000B00122A0003000C3Q00122A0004000D3Q00122A0005000E4Q000D00020005000200100A00010009000200121E0002000A3Q00201900020002000B00122A000300103Q00122A000400103Q00122A000500104Q000D00020005000200100A0001000F00020030010001001100120030010001001300142Q00103Q00017Q00033Q00030E3Q0046696E6446697273744368696C6403133Q00506C617965724553505F486967686C6967687403073Q0044657374726F7901083Q00202300013Q000100122A000300024Q000D0001000300020006090001000700013Q0004173Q000700010020230002000100032Q002B0002000200012Q00103Q00017Q00073Q0003043Q0067616D6503073Q00506C6179657273030B3Q004C6F63616C506C6179657203093Q0043686172616374657203153Q0046696E6446697273744368696C644F66436C612Q7303083Q0048756D616E6F696403093Q0057616C6B53702Q656401113Q00121E000100013Q0020190001000100020020190001000100030020190001000100040006090001000D00013Q0004173Q000D000100121E000100013Q00201900010001000200201900010001000300201900010001000400202300010001000500122A000300064Q000D0001000300020006090001001000013Q0004173Q0010000100100A000100074Q00103Q00017Q00043Q0003023Q005F47030A3Q00496E7374616E742Q507303043Q007461736B03053Q00737061776E01073Q00121E000100013Q00100A000100023Q00121E000100033Q00201900010001000400021D00026Q002B0001000200012Q00103Q00013Q00013Q000C3Q0003023Q005F47030A3Q00496E7374616E742Q507303043Q007461736B03043Q0077616974029A5Q99E93F03053Q00706169727303093Q00776F726B7370616365030E3Q0047657444657363656E64616E74732Q033Q00497341030F3Q0050726F78696D69747950726F6D7074030C3Q00486F6C644475726174696F6E029Q00183Q00121E3Q00013Q0020195Q00020006093Q001700013Q0004173Q0017000100121E3Q00033Q0020195Q000400122A000100054Q002B3Q0002000100121E3Q00063Q00121E000100073Q0020230001000100082Q000F000100024Q00125Q00020004173Q0014000100202300050004000900122A0007000A4Q000D0005000700020006090005001400013Q0004173Q001400010030010004000B000C0006283Q000E000100020004173Q000E00010004175Q00012Q00103Q00017Q00053Q0003023Q005F4703063Q00457370506C7203063Q00697061697273030A3Q00476574506C617965727303093Q00436861726163746572011C3Q00121E000100013Q00100A000100023Q00121E000100034Q002600025Q0020230002000200042Q000F000200034Q001200013Q00030004173Q001900012Q0026000600013Q00061800050019000100060004173Q001900010020190006000500050006090006001900013Q0004173Q0019000100121E000600013Q0020190006000600020006090006001600013Q0004173Q001600012Q0026000600023Q0020190007000500052Q002B0006000200010004173Q001900012Q0026000600033Q0020190007000500052Q002B00060002000100062800010008000100020004173Q000800012Q00103Q00017Q00", GetFEnv(), ...);
